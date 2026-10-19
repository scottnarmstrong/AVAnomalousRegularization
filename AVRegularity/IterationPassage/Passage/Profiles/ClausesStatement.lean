-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.IterationPassage.Cascade.OutputData
import AVRegularity.Construction.Preservation.Residual.KernelReadout.ClassicalComponent
import AVRegularity.Construction.Scales.Times
public import AVRegularity.IterationPassage.Passage.Profiles.DiscardedCov
import AVRegularity.Construction.Preservation.FullLift.KernelStrongEnergy
import AVRegularity.Readout.RepresentationEstimates
import AVRegularity.Readout.OperatorMap
import AVRegularity.Finite.TerminalLift.CovarianceIdentification
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup

section
section
/-! **The error profile, part 1: scale algebra**.

Abstract reals. For `0 < e ≤ 1`, `E^q ≤ 2e`, `c ≥ 0`, `0 < a ≤ 1`, `a e^{1+c} ≤ ρ`,
`z = 1 + s + c(K+1) ≥ 0`:
`∑_{j ≤ K} e^{j-s} ρ^{-j-1} ≤ (K+1) a^{-(K+1)} 2^z E^{-q z}`.
The exponents: `e^{j-s} ρ^{-j-1} ≤ a^{-j-1} e^{j-s-(1+c)(j+1)} = a^{-j-1} e^{-(1+s+c(j+1))}`,
largest at `j = K` (as `e ≤ 1`); then `e ≥ E^q/2` gives `e^{-z} ≤ 2^z E^{-qz}`.
Special cases: `K = 0`; `c = 0`; `e = 1 = E`. -/

@[expose] public noncomputable section

namespace AVRegularity.IterationPassage.Passage

theorem errorProfile_neg_rpow_le {e E q z : ℝ} (hE0 : 0 < E) (hz : 0 ≤ z)
    (hee : E ^ q ≤ 2 * e) : e ^ (-z) ≤ 2 ^ z * E ^ (-(q * z)) := by
  have hEq : 0 < E ^ q := Real.rpow_pos_of_pos hE0 q
  have hlow : 0 < E ^ q / 2 := by positivity
  have h1 : e ^ (-z) ≤ (E ^ q / 2) ^ (-z) :=
    Real.rpow_le_rpow_of_nonpos hlow (by linarith) (by linarith)
  have h2 : (E ^ q / 2) ^ (-z) = 2 ^ z * E ^ (-(q * z)) := by
    rw [Real.div_rpow hEq.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul hE0.le, show q * -z = -(q * z) by ring]
    rw [div_inv_eq_mul, mul_comm]
  rw [h2] at h1
  exact h1

theorem errorProfile_scale_sum_le {e E ρ a c s q : ℝ} {K : ℕ} (he0 : 0 < e) (he1 : e ≤ 1)
    (hE0 : 0 < E) (ha0 : 0 < a) (ha1 : a ≤ 1) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hρ : a * e ^ (1 + c) ≤ ρ) (hee : E ^ q ≤ 2 * e) :
    ∑ j ∈ Finset.range (K + 1), e ^ ((j : ℝ) - s) * ρ ^ (-(j : ℝ) - 1) ≤
      ((K : ℝ) + 1) * ((1 / a) ^ (K + 1) *
        (2 ^ (1 + s + c * ((K : ℝ) + 1)) * E ^ (-(q * (1 + s + c * ((K : ℝ) + 1)))))) := by
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hz : 0 ≤ 1 + s + c * ((K : ℝ) + 1) := by positivity
  have h := Cascade.bottom_scale_sum_le (E := e) (ρ := ρ) (cr := a) (Cr := 1) (c := c) (s := s) (K := K)
    he0 he1 ha0 le_rfl ha1 hc (by simpa using hρ)
  have h2 := errorProfile_neg_rpow_le hE0 hz hee
  refine h.trans ?_
  calc _ ≤ ((K : ℝ) + 1) * ((1 / a) ^ (K + 1) * (2 ^ (1 + s + c * ((K : ℝ) + 1)) *
        E ^ (-(q * (1 + s + c * ((K : ℝ) + 1)))))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **Regularity of the profile kernel on classical fields**.

The paired kernel average `KernelSpec.applyClassical` of a periodic `C^n` field is periodic and
`C^n` (the tensor kernel is a compactly supported smooth kernel, `passage_kernel_sup`'s
`applyClassical_eq_op`, and `kernel_readout_op_contDiff`). Special cases: `n = 0` (continuity);
the zero field (the average is zero); no moment condition on the template is used. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.Analysis.Convolution
open AVRegularity.Providers AVRegularity.Providers.KernelSup AVRegularity.Construction.Preservation.Residual

namespace AVRegularity.IterationPassage.Passage

/-- The kernel average of a periodic `C^n` field is periodic and `C^n`. -/
theorem regularKernel_contDiff_periodic {φ₀ : Vec 2 → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (S : KernelSpec) (t : ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {n : ℕ} {f : Vec 2 → E} (hf : ContDiff ℝ (n : ℕ∞) f) (hp : IsZ2Periodic f) :
    ContDiff ℝ (n : ℕ∞) (S.applyClassical φ₀ t f) ∧ IsZ2Periodic (S.applyClassical φ₀ t f) := by
  have hφc := hasCompactSupport_of_unitBall hφsupp
  have hkK : IsKer (tensorKer (momentKernel φ₀ S.order)) :=
    isKer_tensorKer (contDiff_momentKernel hφc hφs S.order) (hasCompactSupport_momentKernel hφc S.order)
  obtain ⟨B, hB⟩ := bdd_of_periodic hf.continuous hp
  rw [applyClassical_eq_op S _ rfl hkK t hf.continuous hB]
  exact ⟨kernel_readout_op_contDiff hkK _ hf hp, kernel_readout_op_periodic _ _ hp⟩

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The error profile, part 2: the molecular radius against the scales**.

* `errorProfile_eps_step_lower`: for `m ≥ 2`, `ε_{m-1}^q ≤ 2 ε_m` (`⌈x^q⌉ ≤ 2 x^q`, `⌈x⌉ ≥ x`).
* `errorProfile_rhoStar_lower`: above the ledger threshold, for `1 ≤ m < M`, `c₀ ∈ (0,1]`:
  `a c₀ ε_m^{1+c} ≤ ρ_⋆ ≤ 1` with `a = min 1 (C^{-1/2})`. Exponents: `κ_m ≍ ε_m^{1+α+γ}`,
  `a_m = ε_m^{α-1}`, so `√(κ_m/a_m) ≍ ε_m^{1+γ/2} ≥ ε_m^{1+c}` as `c = γ/2 + δ`, `δ > 0`, `ε_m ≤ 1`. -/

@[expose] public noncomputable section

namespace AVRegularity.IterationPassage.Passage

open AVRegularity

theorem errorProfile_eps_step_lower {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (hm : 2 ≤ m) :
    ocEpsilon q Λ (m - 1) ^ q ≤ 2 * ocEpsilon q Λ m := by
  have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  set x : ℝ := (Λ : ℝ) ^ (q ^ (m - 1) / (q - 1)) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow (by linarith) (by
    have : 0 < q - 1 := by linarith
    have : 1 ≤ q ^ (m - 1) := one_le_pow₀ hq.le
    positivity)
  have hxq : x ^ q = (Λ : ℝ) ^ (q ^ m / (q - 1)) := by
    rw [hx, ← Real.rpow_mul (by linarith)]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  have h1 : ocEpsilon q Λ (m - 1) = (⌈x⌉₊ : ℝ)⁻¹ := by
    simp [ocEpsilon, show m - 1 ≠ 0 by omega, hx]
  have h2 : ocEpsilon q Λ m = (⌈x ^ q⌉₊ : ℝ)⁻¹ := by
    simp [ocEpsilon, show m ≠ 0 by omega, hxq]
  have hxq1 : 1 ≤ x ^ q := Real.one_le_rpow hx1 (by linarith)
  have hxpos : 0 < x := by linarith
  have hxqpos : 0 < x ^ q := by linarith
  have hc1 : (⌈x ^ q⌉₊ : ℝ) ≤ 2 * x ^ q := by
    have := Nat.ceil_lt_add_one hxqpos.le
    linarith
  have hc0 : (0 : ℝ) < ⌈x ^ q⌉₊ := by exact_mod_cast Nat.ceil_pos.mpr hxqpos
  have hcx : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  rw [h1, h2]
  have h3 : ((⌈x⌉₊ : ℝ)⁻¹) ^ q ≤ (x⁻¹) ^ q :=
    Real.rpow_le_rpow (by positivity) (inv_anti₀ hxpos hcx) (by linarith)
  rw [Real.inv_rpow hxpos.le] at h3
  refine h3.trans ?_
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hxqpos hc0]
  linarith

theorem errorProfile_rhoStar_lower {D : OCData} {c₀ C : ℝ} {m : ℕ} (hq : 1 < D.q)
    (hΛ : 128 ≤ D.Λ) (hC : 1 ≤ C) (hc0 : 0 < c₀) (hc1 : c₀ ≤ 1)
    (hδ : 0 ≤ ocDelta D.α D.q) (hγ : 0 ≤ ocGamma D.α D.q)
    (hκ : ocAsymp C (D.κ m) (ocEpsilon D.q D.Λ m ^ ((1 + D.α) + ocGamma D.α D.q))) :
    c₀ / C * D.eps m ^ (1 + ocC D.α D.q) ≤ rhoStar D c₀ m ∧ rhoStar D c₀ m ≤ 1 := by
  obtain ⟨he0, he1, -⟩ := Scales.epsilon_basic (m := m) hq hΛ
  have hE : D.eps m = ocEpsilon D.q D.Λ m := rfl
  rw [hE]
  have hA : ocA D.α D.q D.Λ m = ocEpsilon D.q D.Λ m ^ ((1 + D.α) - 2) := rfl
  set e := ocEpsilon D.q D.Λ m with he
  have hC0 : 0 < C := by linarith
  have hCi : C⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC
  have hCi0 : 0 < C⁻¹ := inv_pos.mpr hC0
  set g := ocGamma D.α D.q with hg
  have hcc : ocC D.α D.q = g / 2 + ocDelta D.α D.q := rfl
  have hpow1 : e ^ (1 + ocC D.α D.q) ≤ e := by
    calc e ^ (1 + ocC D.α D.q) ≤ e ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_ge he0 he1
          rw [hcc]; linarith
      _ = e := Real.rpow_one e
  have hApos : 0 < e ^ ((1 + D.α) - 2) := Real.rpow_pos_of_pos he0 _
  have hmul : e ^ (2 + g) * e ^ ((1 + D.α) - 2) = e ^ ((1 + D.α) + g) := by
    rw [← Real.rpow_add he0]; congr 1; ring
  have hq1 : C⁻¹ * e ^ (2 + g) ≤ D.κ m / ocA D.α D.q D.Λ m := by
    rw [hA, le_div_iff₀ hApos, mul_assoc, hmul]
    exact hκ.1
  have hsq : (C⁻¹ * e ^ (1 + ocC D.α D.q)) ^ 2 ≤ C⁻¹ * e ^ (2 + g) := by
    have h1 : (e ^ (1 + ocC D.α D.q)) ^ 2 = e ^ (2 * (1 + ocC D.α D.q)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul he0.le]; norm_num; rw [mul_comm]
    have h2 : e ^ (2 * (1 + ocC D.α D.q)) ≤ e ^ (2 + g) := by
      apply Real.rpow_le_rpow_of_exponent_ge he0 he1
      rw [hcc]; linarith
    calc (C⁻¹ * e ^ (1 + ocC D.α D.q)) ^ 2 = C⁻¹ * C⁻¹ * (e ^ (1 + ocC D.α D.q)) ^ 2 := by ring
      _ ≤ 1 * C⁻¹ * e ^ (2 + g) := by
          rw [h1]; gcongr
      _ = _ := by ring
  have hy0 : 0 ≤ C⁻¹ * e ^ (1 + ocC D.α D.q) := by positivity
  have hyle : C⁻¹ * e ^ (1 + ocC D.α D.q) ≤ min e (Real.sqrt (D.κ m / ocA D.α D.q D.Λ m)) := by
    refine le_min ?_ ?_
    · calc _ ≤ 1 * e ^ (1 + ocC D.α D.q) := by gcongr
        _ ≤ e := by linarith
    · exact Real.le_sqrt_of_sq_le (hsq.trans hq1)
  have hmin : min e (Real.sqrt (D.κ m / ocA D.α D.q D.Λ m)) ≤ 1 := (min_le_left _ _).trans he1
  have hmin0 : 0 ≤ min e (Real.sqrt (D.κ m / ocA D.α D.q D.Λ m)) := hy0.trans hyle
  refine ⟨?_, ?_⟩
  · unfold rhoStar
    calc c₀ / C * e ^ (1 + ocC D.α D.q) = c₀ * (C⁻¹ * e ^ (1 + ocC D.α D.q)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hyle hc0.le
  · unfold rhoStar
    calc c₀ * min e _ ≤ 1 * 1 := mul_le_mul hc1 hmin hmin0 zero_le_one
      _ = 1 := one_mul 1

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **Scaled Sobolev to profile, part 3: derivatives and components**.

* `partialDerivative α f = orderedDerivative (word α) f` for every `f` (the word has `α₀` zeros
  followed by `α₁` ones), so the `partialDerivative` of the profile norm is an ordered
  derivative of the classical representative.
* `sobolevProfile_component_sq`: for one component `X ∈ H^{K+2}` and a continuous periodic `C^K`
  function `g_v` equal a.e. on the cell to the value jet of `X`, every `∂^α g_v`, `|α| = j ≤ K`,
  has `(∂^α g_v)² ≤ C ρ^{-(2j+2)} ‖X‖²_{ρ,K+2}` (the classical representative of `X` is `g_v`).
* `sobolevProfile_coord`: the `v`-th coordinate of `∂^α (compField π g)` is `π_v^{-1/2} ∂^α g_v`.
Special cases: `α = 0` (the sup bound of the amplitude); `X = 0`, `g_v = 0`. -/

@[expose] public noncomputable section

namespace AVRegularity.IterationPassage.Passage

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity

/-- The ordered word with `α₀` zeros followed by `α₁` ones. -/
def sobolevProfileWord (α : Fin 2 → ℕ) : DerivativeWord2 (α 0 + α 1) :=
  fun i => if i.val < α 0 then 0 else 1

theorem sobolevProfile_foldl_replicate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 2) (n : ℕ) (G : Vec 2 → E) :
    (List.replicate n i).foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) G =
      (fun G : Vec 2 → E => fun x => fderiv ℝ G x (basisVec i))^[n] G := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons, Function.iterate_succ_apply]
    exact ih _

theorem sobolevProfile_ofFn_word (α : Fin 2 → ℕ) :
    List.ofFn (sobolevProfileWord α) = List.replicate (α 0) 0 ++ List.replicate (α 1) 1 := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_ofFn, sobolevProfileWord, List.getElem_append, List.getElem_replicate,
      List.length_replicate]
    by_cases h : n < α 0
    · simp [h]
    · simp [h]

theorem sobolevProfile_partialDerivative_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : Fin 2 → ℕ) (f : Vec 2 → E) :
    partialDerivative α f = orderedDerivative (sobolevProfileWord α) f := by
  unfold orderedDerivative partialDerivative
  rw [sobolevProfile_ofFn_word, List.foldl_append, sobolevProfile_foldl_replicate,
    sobolevProfile_foldl_replicate]

/-- One component: the classical representative of `X ∈ H^{K+2}` is `g_v`, and the scaled sup
bound applies to every `∂^α g_v`, `|α| ≤ K`. -/
theorem sobolevProfile_component_sq {K : ℕ} (X : TorusHk (K + 2) ℝ) (gv : Vec 2 → ℝ)
    (hc : ContDiff ℝ (K : ℕ) gv) (hp : AVenhance.IsZ2Periodic gv)
    (hX : X.toFunction.jet (valueIndex2 (K + 2)) =ᵐ[volume.restrict AVenhance.unitCube] gv)
    (α : Fin 2 → ℕ) (hα : α 0 + α 1 ≤ K) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (x : Vec 2) :
    (partialDerivative α gv x) ^ 2 ≤
      sobolevScaledConst (K + 2) * (ρ ^ (2 * (α 0 + α 1) + 2))⁻¹ * factorialNormSq ρ X.val := by
  obtain ⟨a, ha⟩ := Construction.Preservation.FullLift.hilbert_classicalRep_exists (K + 2) K
    (le_refl _) X
  have hval : a =ᵐ[volume.restrict AVenhance.unitCube] gv := by
    have h0 := ha.2.2.2 0 (Nat.zero_le _) Fin.elim0
    have h1 : torusJetOrder X 0 Fin.elim0 = X.toFunction.jet (valueIndex2 (K + 2)) := by
      funext y
      simp [torusJetOrder, valueIndex2, valueIndex]
    rw [h1] at h0
    have h2 : orderedDerivative (Fin.elim0 : DerivativeWord2 0) a = a := rfl
    rw [h2] at h0
    exact h0.symm.trans hX
  have hag : a = gv := CycleComparison.Lift.periodicContinuous_eq_of_cell_ae a gv
    ha.2.1.continuous hc.continuous ha.2.2.1 hp hval
  rw [sobolevProfile_partialDerivative_eq, ← hag]
  exact sobolevScaledSup_classical_sq X a ha hα (sobolevProfileWord α) hρ hρ1 x

end AVRegularity.IterationPassage.Passage
end
end
end

section
section
/-! **The profile proposition of one passage from its parts**.

`PassageClauses` is assembled from four facts about the
five profiles of `passageProfiles` at each time of the window, for given classical representatives
`aU`, `aY` and lift coefficients `CcT`:

* `ProfilesRegular`: each profile field is of class `C^K` and `ℤ²`-periodic;
* `ProfilesSplit`: the exact identity (13.11) of the paper, in the form
  `∑ (five profiles) = F(aU) - 𝖱F'(aY)` in normalized coordinates;
* `RetainedBounds`: `𝓘_{E,K;s}(H_E) ≤ CE^{δ-2σ₀}[Y]_{E,K;s}` and `𝓘_{e,K;s}(H_e) ≤ CE^{μ_s}[Y]_{E,K;s}`;
* `DiscardedBounds`: `𝓘_{E,K;s}(D_E) + 𝓘_{e,K;s}(D_e) + 𝓘_{e,K;s}(𝓔) ≤ CE^PA`;

together with the existence of the representatives and the readout norm
`‖𝖱‖ ≤ 1 + CE^{5η₀/4}`. The recurrence of the passage follows by copying the
representation of `Y(t)` through `𝖱` (`Readout.representedSize_map_le`, wavelength restriction
`Readout.profileSeminorm_le_label`), `[Y]_{E,K;s} ≤ X_E(Y)` (`Readout.representation_profile_readout`)
and appending the five profiles.

`append_representation` is the general statement: a representation at `E` copied by a constant map
with profiles of labels in `[e, 1]` appended.

Special cases. An empty incoming family: all fields are the zero function of the trivial space and
every bound is `0 ≤ ·`. `A = 0`: the discarded bound forces the three profiles to vanish, and the
recurrence has no inhomogeneous term. `K = 0` is excluded by the caller (`3 ≤ K`); the lemmas here
do not use it. The constant `C ≥ 0` is one constant for the readout norm and the two bounds. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- A representation at the wavelength `E`, copied by a constant map `R`, with appended profiles of
labels in `[e, 1]` whose values sum to `u - R(value)`: it is a representation of `u` at `e`, and
its size is at most `‖R‖` times the old size plus the norms of the appended profiles. -/
theorem append_representation {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H'] {s e E : ℝ} {K : ℕ} (hs₁ : s < 1) (he : 0 < e)
    (heE : e ≤ E) (R : H →L[ℝ] H') (rY : Representation H) (hr : IsRepresentationAt E K rY)
    (l : List ((Vec 2 → H') × ℝ))
    (hl : ∀ q ∈ l, ContDiff ℝ (K : ℕ) q.1 ∧ IsZ2Periodic q.1 ∧ e ≤ q.2 ∧ q.2 ≤ 1)
    (u : Vec 2 → H') (hsum : ∀ x, (l.map fun q => q.1 x).sum = u x - R (rY.value x)) (Cn : ℝ)
    (hR : ‖R‖ ≤ Cn) :
    IsRepresentationAt e K ⟨(rY.map R).base, (rY.map R).profiles ++ l⟩ ∧
      (⟨(rY.map R).base, (rY.map R).profiles ++ l⟩ : Representation H').value = u ∧
      representedSize s K e ⟨(rY.map R).base, (rY.map R).profiles ++ l⟩ ≤
        ENNReal.ofReal Cn * representedSize s K E rY +
          (l.map fun q => profileNorm q.2 K s q.1).sum := by
  have hp := Finite.TerminalLift.prefix_representation he heE le_rfl rY R hr
  refine ⟨⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, fun q hq => ?_⟩, ?_, ?_⟩
  · rcases List.mem_append.mp hq with h | h
    · exact hp.2.2.2.2 q h
    · exact hl q h
  · funext x
    have h := congrFun (Readout.representation_map_value rY R) x
    simp only [Representation.value] at h
    simp only [Representation.value, List.map_append, List.sum_append]
    rw [← add_assoc, h, hsum x]
    exact add_sub_cancel _ _
  · have hsize : representedSize s K e ⟨(rY.map R).base, (rY.map R).profiles ++ l⟩ =
        representedSize s K e (rY.map R) + (l.map fun q => profileNorm q.2 K s q.1).sum := by
      simp only [representedSize, List.map_append, List.sum_append]
      ac_rfl
    rw [hsize]
    exact add_le_add (Finite.TerminalLift.prefix_size_le he heE hs₁ le_rfl rY R hr hR) le_rfl

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Each of the five profile fields at the time `t` is of class `C^K` and periodic. -/
def ProfilesRegular (D : OCData) (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth K : ℕ) (η₀ : ℝ) (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ) : Prop :=
  ∀ q ∈ passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY,
    ContDiff ℝ (K : ℕ) (q.1 t) ∧ IsZ2Periodic (q.1 t)

/-- The exact identity (13.11) of the paper at the time `t`: the five profiles sum to
`U - 𝖱Y` in normalized coordinates. -/
def ProfilesSplit (D : OCData) (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth : ℕ) (η₀ : ℝ) (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ) : Prop :=
  ∀ x, ((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map fun q => q.1 t x).sum =
    compField (G.mass law) (aU t) x -
      readoutCLM m (D.eps (m - 1)) η₀ (G.mass law) (Gr.mass law)
        (compField (Gr.mass law) (aY t) x)

/-- The bounds of the retained profiles `H_E`, `H_e` at the time `t`. -/
def RetainedBounds (D : OCData) (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth K : ℕ) (s η₀ mu wexp C : ℝ) (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ) : Prop :=
  profileNorm (D.eps (m - 1)) K s
      (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map fun q => q.1 t).getD 0 0) ≤
    ENNReal.ofReal (C * D.eps (m - 1) ^ wexp) *
      profileSeminorm (D.eps (m - 1)) K s (compField (Gr.mass law) (aY t)) ∧
  profileNorm (D.eps m) K s
      (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map fun q => q.1 t).getD 1 0) ≤
    ENNReal.ofReal (C * D.eps (m - 1) ^ mu) *
      profileSeminorm (D.eps (m - 1)) K s (compField (Gr.mass law) (aY t))

/-- The bound of the discarded profiles `D_E`, `D_e` and of the error `𝓔` at the time `t`. -/
def DiscardedBounds (D : OCData) (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth K : ℕ) (s η₀ P C A : ℝ) (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ) : Prop :=
  profileNorm (D.eps (m - 1)) K s
      (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map fun q => q.1 t).getD 2 0) +
    profileNorm (D.eps m) K s
      (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map fun q => q.1 t).getD 3 0) +
    profileNorm (D.eps m) K s
      (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map fun q => q.1 t).getD 4 0) ≤
    ENNReal.ofReal (C * D.eps (m - 1) ^ P * A)

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **`PassageClauses` from the parts**.

`passageClauses_of_parts`: the exact profile proposition of one passage from the existence of
the classical representatives, the readout norm, and, for all representatives, lifts and times, the
four facts `ProfilesRegular`, `ProfilesSplit`, `RetainedBounds` and `DiscardedBounds`. All four
facts and the readout norm are taken with the same constant `C ≥ 0`.

If no representatives exist the statement is false, which is why their existence is a hypothesis
here and a separate ingredient. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The labels of the five profiles are `E, e, E, e, e`. -/
theorem passageProfiles_label (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth : ℕ) (η₀ : ℝ) (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) :
    ∀ q ∈ passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY,
      q.2 = D.eps (m - 1) ∨ q.2 = D.eps m := by
  intro q hq
  simp only [passageProfiles, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- The sum of the profile norms of the five profiles at the time `t`, with their labels. -/
theorem passageProfiles_norm_sum (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth K : ℕ) (s η₀ : ℝ) (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root) (t : ℝ) :
    (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
        fun q => (q.1 t, q.2)).map fun q => profileNorm q.2 K s q.1).sum =
      profileNorm (D.eps (m - 1)) K s
          (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
            fun q => q.1 t).getD 0 0) +
        profileNorm (D.eps m) K s
          (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
            fun q => q.1 t).getD 1 0) +
        (profileNorm (D.eps (m - 1)) K s
            (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
              fun q => q.1 t).getD 2 0) +
          profileNorm (D.eps m) K s
            (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
              fun q => q.1 t).getD 3 0) +
          profileNorm (D.eps m) K s
            (((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
              fun q => q.1 t).getD 4 0)) := by
  simp only [passageProfiles, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.getD_cons_zero, List.getD_cons_succ, add_zero]
  ac_rfl

/-- **The exact profile proposition of one passage from its parts.** -/
theorem passageClauses_of_parts (law : BirthLaw) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth sX sZ K : ℕ) (s η₀ mu wexp P C A tp tf : ℝ) (φ₀ : Vec 2 → ℝ) (Sr : KernelSpec)
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (hs₀ : 0 < s) (hs₁ : s < 1) (he : 0 < D.eps m) (heE : D.eps m ≤ D.eps (m - 1)) (hC : 0 ≤ C)
    (hRn : ‖readoutCLM m (D.eps (m - 1)) η₀ (G.mass law) (Gr.mass law)‖ ≤
      1 + C * D.eps (m - 1) ^ (5 * η₀ / 4))
    (hsmooth : ∃ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
        (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root),
      (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => U v t) (aU t) (K + N + 2 * p + 2)) ∧
      (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => Y v t) (aY t) (K + N + 2 * p + 2)))
    (hparts : ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
        (aY : ℝ → Vec 2 → ∀ v : CompIn Gr.comps, ScalarH v.1.root),
      (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => U v t) (aU t) (K + N + 2 * p + 2)) →
      (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => Y v t) (aY t) (K + N + 2 * p + 2)) →
      ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
        IsPassageLift G m N depth sX sZ CcT →
      ∀ t ∈ Set.Icc tp tf,
        ProfilesRegular D law G Gr m p N depth K η₀ φ₀ Sr CcT aU aY t ∧
        ProfilesSplit D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY t ∧
        RetainedBounds D law G Gr m p N depth K s η₀ mu wexp C φ₀ Sr CcT aU aY t ∧
        DiscardedBounds D law G Gr m p N depth K s η₀ P C A φ₀ Sr CcT aU aY t) :
    PassageClauses D law G Gr m p N depth sX sZ K s η₀ mu wexp P C A tp tf φ₀ Sr U Y := by
  refine ⟨hsmooth, fun aU aY haU haY CcT hCcT t ht => ?_⟩
  obtain ⟨hreg, hsplit, hret, hdis⟩ := hparts aU aY haU haY CcT hCcT t ht
  refine ⟨hret.1, hret.2, hdis, fun rY hrY hval => ?_⟩
  have hE0 : 0 < D.eps (m - 1) := hrY.1
  have hE1 : D.eps (m - 1) ≤ 1 := hrY.2.1
  have hl : ∀ q ∈ (passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map
      (fun q => (q.1 t, q.2)),
      ContDiff ℝ (K : ℕ) q.1 ∧ IsZ2Periodic q.1 ∧ D.eps m ≤ q.2 ∧ q.2 ≤ 1 := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    refine ⟨(hreg q' hq').1, (hreg q' hq').2, ?_, ?_⟩
    · rcases passageProfiles_label law G Gr m p N depth η₀ φ₀ Sr CcT aU aY q' hq' with h | h
      · exact h ▸ heE
      · exact h ▸ le_rfl
    · rcases passageProfiles_label law G Gr m p N depth η₀ φ₀ Sr CcT aU aY q' hq' with h | h
      · exact h ▸ hE1
      · exact h ▸ heE.trans hE1
  obtain ⟨h1, h2, h3⟩ := append_representation (s := s) hs₁ he heE
    (readoutCLM m (D.eps (m - 1)) η₀ (G.mass law) (Gr.mass law)) rY hrY
    ((passageProfiles D law G Gr m p N depth η₀ φ₀ Sr CcT aU aY).map fun q => (q.1 t, q.2)) hl
    (compField (G.mass law) (aU t))
    (by
      intro x
      rw [List.map_map, hval]
      exact hsplit x) _ hRn
  refine ⟨h1, h2, h3.trans ?_⟩
  have hYE : profileSeminorm (D.eps (m - 1)) K s (compField (Gr.mass law) (aY t)) ≤
      representedSize s K (D.eps (m - 1)) rY := by
    have h := Readout.representation_profile_readout hs₀ hs₁ rY hrY
    rw [hval] at h
    exact le_add_self.trans h
  have hn : 0 ≤ D.eps (m - 1) ^ (5 * η₀ / 4) := Real.rpow_nonneg hE0.le _
  have hm : 0 ≤ D.eps (m - 1) ^ mu := Real.rpow_nonneg hE0.le _
  have hw : 0 ≤ D.eps (m - 1) ^ wexp := Real.rpow_nonneg hE0.le _
  rw [passageProfiles_norm_sum]
  calc ENNReal.ofReal (1 + C * D.eps (m - 1) ^ (5 * η₀ / 4)) *
          representedSize s K (D.eps (m - 1)) rY + _
      ≤ ENNReal.ofReal (1 + C * D.eps (m - 1) ^ (5 * η₀ / 4)) *
          representedSize s K (D.eps (m - 1)) rY +
        (ENNReal.ofReal (C * D.eps (m - 1) ^ wexp) * representedSize s K (D.eps (m - 1)) rY +
          ENNReal.ofReal (C * D.eps (m - 1) ^ mu) * representedSize s K (D.eps (m - 1)) rY +
          ENNReal.ofReal (C * D.eps (m - 1) ^ P * A)) :=
        add_le_add le_rfl (add_le_add (add_le_add
          (hret.1.trans (mul_le_mul' le_rfl hYE)) (hret.2.trans (mul_le_mul' le_rfl hYE))) hdis)
    _ = ENNReal.ofReal (1 + C * (D.eps (m - 1) ^ (5 * η₀ / 4) + D.eps (m - 1) ^ mu +
          D.eps (m - 1) ^ wexp)) * representedSize s K (D.eps (m - 1)) rY +
        ENNReal.ofReal (C * D.eps (m - 1) ^ P * A) := by
        have hsum : 1 + C * (D.eps (m - 1) ^ (5 * η₀ / 4) + D.eps (m - 1) ^ mu +
            D.eps (m - 1) ^ wexp) = (1 + C * D.eps (m - 1) ^ (5 * η₀ / 4)) +
              C * D.eps (m - 1) ^ wexp + C * D.eps (m - 1) ^ mu := by ring
        rw [hsum, ENNReal.ofReal_add (add_nonneg (add_nonneg zero_le_one (mul_nonneg hC hn))
            (mul_nonneg hC hw)) (mul_nonneg hC hm),
          ENNReal.ofReal_add (add_nonneg zero_le_one (mul_nonneg hC hn)) (mul_nonneg hC hw),
          add_mul, add_mul, add_assoc, add_assoc, add_assoc]

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The ingredients of the profile proposition of one passage**.

`PassageClauses` is assembled from four facts about the five profiles
(`passageClauses_of_parts`). The statements below give these facts. The five prefix statements
have the prefix of `iteration_passage` through the carrier start and the data of a passage
`m → m-1` (cascade stage `G` with its invariant on `[t_A, t_f]`, actual successor `G'`, times
`t_A + 3τ_m ≤ s₀`, `s₀ + 4τ_m'' ≤ t_f`, `t_f - s₀ ≤ T₀`); then they speak about ARBITRARY
classical fields at one time `t ∈ [s₀, t_f]`: no solution enters. The profiles at the time `t`
depend on `aU t`, `aY t` only.

* `PassageProfilesRegularStatement`: for `C^{K+N+2p+2}` periodic `aU t`, `aY t` and actual lift
  coefficients, the five profile fields are `C^K` and periodic, and they sum to `F(aU) - 𝖱F'(aY)`.
* `PassageRetainedCovarianceStatement`: `𝓘_{E,K;s}(H_E) ≤ CE^{δ-2σ₀}[F'aY]_{E,K;s}`, and
  `PassageRetainedLiftStatement`: `𝓘_{e,K;s}(H_e) ≤ CE^{μ_s}[F'aY]_{E,K;s}`, each given a bound
  `C_n` of the readout norm.
* `PassageDiscardedProfilesStatement`: `𝓘_{E,K;s}(D_E) + 𝓘_{e,K;s}(D_e) ≤ CE^P B` when `aY t` is the
  classical representative of an `H^{N_aux}` family of marked weighted norm `≤ B` at the radius
  `ρ = rhoEnh`, given `C_n`.
* `PassageErrorProfileStatement`: `𝓘_{e,K;s}(g) ≤ CE^{-qZ_K}B` when `g` is the classical
  representative of an `H^{K+2}` family of weighted norm `≤ B` at the radius `ρ_⋆ = rhoStar`.
* `SmoothRepOfHigherStatement` (local): a family with an `H^n` lift, `k + 2 ≤ n`, has a classical
  periodic `C^k` representative.

Special cases. Empty families: the fields are functions into the trivial space, all norms are `0`.
`B = 0`: the family vanishes almost everywhere, hence its continuous representative vanishes, and
the profile norms are `0`. `aY t = 0`: all four retained and discarded profiles vanish (the
operators are linear). A constant field `aY t`: `[F'aY]_{E,K;s} = 0`, so the retained profiles must
vanish; they do, because every monomial of `P_p - I` and of `T - I` differentiates its argument at
least once (`C_0 = I`; the monomials `c_{n,d}D^d` have `1 ≤ d`). Constants: `C_n` before `C₀`,
`m_*`; all statements are closed upward in `C`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- Data part of `PassageProfilesRegularStatement`: regularity of the five profiles and the exact split. -/
def PassageProfilesRegularData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (bw : ℝ) (K : ℕ) (T₀ : ℝ) (r₀ D₀ : ℕ) (τe : ℝ) (H J N p nk npad : ℕ)
    (σ₀ : ℝ) (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
      IsPassageLift G m N (succSchedR r₀ J H) sX sZ CcT →
    ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (G'.retained m H J).comps, ScalarH v.1.root) (t : ℝ),
      s₀ ≤ t → t ≤ tf →
      ContDiff ℝ (K + N + 2 * p + 2 : ℕ) (aU t) → IsZ2Periodic (aU t) →
      ContDiff ℝ (K + N + 2 * p + 2 : ℕ) (aY t) → IsZ2Periodic (aY t) →
      ProfilesRegular D law G (G'.retained m H J) m p N (succSchedR r₀ J H) K (succEta0 α q s) φ₀ (freshK (m - 1)) CcT aU aY t ∧
      ProfilesSplit D law G (G'.retained m H J) m p N (succSchedR r₀ J H) (succEta0 α q s) φ₀ (freshK (m - 1)) CcT aU aY t

/-- **Regularity of the profiles and the split identity**. -/
def PassageProfilesRegularStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc : ℝ), 3 ≤ K → 0 < Pacc →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ → Pacc + q * iterZ α q s K + 4 < Q / 2 →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
    ∀ L : ℕ, IsPassageOrders α q s K Pacc σ₀ L N p nk Naux →
      IsCascadeWidths α q lamE a σ (succDstar D₀ N p H) →
    ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ mStar : ℕ,
    PassageProfilesRegularData α s q ζ Λ φ₀ hφ₀ bw K T₀ r₀ D₀ τe H J N p nk npad σ₀ sX sZ Ce kS kI
      CI Cw j₀ mStar

/-- Data part of `PassageRetainedCovarianceStatement`: bound of the retained profile `H_E = 𝖱(P_p - I)S_rY`. -/
def PassageRetainedCovarianceData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (bw : ℝ) (K : ℕ) (T₀ : ℝ) (r₀ D₀ : ℕ) (τe : ℝ) (H J N p nk npad : ℕ)
    (σ₀ : ℝ) (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (Cn C : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ‖readoutCLM m (D.eps (m - 1)) (succEta0 α q s) (G.mass law) ((G'.retained m H J).mass law)‖ ≤ Cn →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
      IsPassageLift G m N (succSchedR r₀ J H) sX sZ CcT →
    ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (G'.retained m H J).comps, ScalarH v.1.root) (t : ℝ),
      s₀ ≤ t → t ≤ tf →
      ContDiff ℝ (K + N + 2 * p + 2 : ℕ) (aY t) → IsZ2Periodic (aY t) →
      profileNorm (D.eps (m - 1)) K s (((passageProfiles D law G (G'.retained m H J) m p N (succSchedR r₀ J H) (succEta0 α q s) φ₀ (freshK (m - 1)) CcT aU aY).map fun q => q.1 t).getD 0 0) ≤
        ENNReal.ofReal (C * D.eps (m - 1) ^ (ocDelta α q - 2 * σ₀)) *
          profileSeminorm (D.eps (m - 1)) K s (compField ((G'.retained m H J).mass law) (aY t))

/-- **The retained covariance profile** `𝓘_{E,K;s}(H_E) ≤ CE^{δ-2σ₀}[Y]_{E,K;s}`, closed upward in
`C`. -/
def PassageRetainedCovarianceStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc : ℝ), 3 ≤ K → 0 < Pacc →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ → Pacc + q * iterZ α q s K + 4 < Q / 2 →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
    ∀ L : ℕ, IsPassageOrders α q s K Pacc σ₀ L N p nk Naux →
      IsCascadeWidths α q lamE a σ (succDstar D₀ N p H) →
    ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ Cn : ℝ, ∃ (C₀ : ℝ) (mStar : ℕ), ∀ C : ℝ, C₀ ≤ C →
    PassageRetainedCovarianceData α s q ζ Λ φ₀ hφ₀ bw K T₀ r₀ D₀ τe H J N p nk npad σ₀ sX sZ Ce kS
      kI CI Cw j₀ Cn C mStar

/-- Data part of `PassageRetainedLiftStatement`: bound of the retained profile `H_e = (T - I)P_p𝖱S_rY`. -/
def PassageRetainedLiftData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw : ℝ) (K : ℕ) (T₀ : ℝ) (r₀ D₀ : ℕ) (τe : ℝ) (H J N p nk npad : ℕ) (σ₀ : ℝ) (sX sZ : ℕ)
    (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (Cn C : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ‖readoutCLM m (D.eps (m - 1)) (succEta0 α q s) (G.mass law) ((G'.retained m H J).mass law)‖ ≤ Cn →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
      IsPassageLift G m N (succSchedR r₀ J H) sX sZ CcT →
    ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (G'.retained m H J).comps, ScalarH v.1.root) (t : ℝ),
      s₀ ≤ t → t ≤ tf →
      ContDiff ℝ (K + N + 2 * p + 2 : ℕ) (aY t) → IsZ2Periodic (aY t) →
      profileNorm (D.eps m) K s (((passageProfiles D law G (G'.retained m H J) m p N (succSchedR r₀ J H) (succEta0 α q s) φ₀ (freshK (m - 1)) CcT aU aY).map fun q => q.1 t).getD 1 0) ≤
        ENNReal.ofReal (C * D.eps (m - 1) ^ ocMuS α q s) *
          profileSeminorm (D.eps (m - 1)) K s (compField ((G'.retained m H J).mass law) (aY t))

/-- **The retained lift profile** `𝓘_{e,K;s}(H_e) ≤ CE^{μ_s}[Y]_{E,K;s}`, closed upward in `C`. -/
def PassageRetainedLiftStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc : ℝ), 3 ≤ K → 0 < Pacc →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ → Pacc + q * iterZ α q s K + 4 < Q / 2 →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
    ∀ L : ℕ, IsPassageOrders α q s K Pacc σ₀ L N p nk Naux →
      IsCascadeWidths α q lamE a σ (succDstar D₀ N p H) →
    ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ Cn : ℝ, ∃ (C₀ : ℝ) (mStar : ℕ), ∀ C : ℝ, C₀ ≤ C →
    PassageRetainedLiftData α s q ζ Λ φ₀ hφ₀ bw K T₀ r₀ D₀ τe H J N p nk npad σ₀ sX sZ Ce kS kI CI
      Cw j₀ Cn C mStar

/-- Data part of `PassageDiscardedProfilesStatement`: bound of the discarded profiles `D_E`, `D_e`. -/
def PassageDiscardedProfilesData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (bw : ℝ) (K : ℕ) (Pacc T₀ : ℝ) (r₀ D₀ : ℕ) (τe : ℝ)
    (H J N p nk Naux npad : ℕ) (σ₀ : ℝ) (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ)
    (j₀ : ℕ) (Cn C : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ‖readoutCLM m (D.eps (m - 1)) (succEta0 α q s) (G.mass law) ((G'.retained m H J).mass law)‖ ≤ Cn →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
      IsPassageLift G m N (succSchedR r₀ J H) sX sZ CcT →
    ∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (G'.retained m H J).comps, ScalarH v.1.root) (t : ℝ),
      s₀ ≤ t → t ≤ tf →
      ContDiff ℝ (K + N + 2 * p + 2 : ℕ) (aY t) → IsZ2Periodic (aY t) →
    ∀ (Yn : ∀ v : CompIn (G'.retained m H J).comps, TorusHk Naux (ScalarH v.1.root)) (B : ℝ),
      (∀ v, (Yn v).toFunction.jet (valueIndex2 Naux) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => aY t x v) →
      weightedNorm (rhoEnh D kI.cr m) ((G'.retained m H J).mass law) ((G'.retained m H J).marker law) Yn ≤ B →
      profileNorm (D.eps (m - 1)) K s (((passageProfiles D law G (G'.retained m H J) m p N (succSchedR r₀ J H) (succEta0 α q s) φ₀ (freshK (m - 1)) CcT aU aY).map fun q => q.1 t).getD 2 0) +
          profileNorm (D.eps m) K s (((passageProfiles D law G (G'.retained m H J) m p N (succSchedR r₀ J H) (succEta0 α q s) φ₀ (freshK (m - 1)) CcT aU aY).map fun q => q.1 t).getD 3 0) ≤
        ENNReal.ofReal (C * D.eps (m - 1) ^ Pacc * B)

/-- **The discarded profiles**, closed upward in `C`. -/
def PassageDiscardedProfilesStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc : ℝ), 3 ≤ K → 0 < Pacc →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ → Pacc + q * iterZ α q s K + 4 < Q / 2 →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
    ∀ L : ℕ, IsPassageOrders α q s K Pacc σ₀ L N p nk Naux →
      IsCascadeWidths α q lamE a σ (succDstar D₀ N p H) →
    ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ Cn : ℝ, ∃ (C₀ : ℝ) (mStar : ℕ), ∀ C : ℝ, C₀ ≤ C →
    PassageDiscardedProfilesData α s q ζ Λ φ₀ hφ₀ bw K Pacc T₀ r₀ D₀ τe H J N p nk Naux npad σ₀ sX
      sZ Ce kS kI CI Cw j₀ Cn C mStar

/-- Data part of `PassageErrorProfileStatement`: Sobolev bound of a profile at the molecular radius of level `m`. -/
def PassageErrorProfileData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw : ℝ) (K : ℕ) (T₀ : ℝ) (r₀ D₀ : ℕ) (τe : ℝ) (H J N p nk npad : ℕ) (σ₀ : ℝ) (sX sZ : ℕ)
    (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (C : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (g : Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root) (t : ℝ), s₀ ≤ t → t ≤ tf →
      ContDiff ℝ (K : ℕ) (compField (G.mass law) g) → IsZ2Periodic (compField (G.mass law) g) →
    ∀ (En : ∀ v : CompIn G.comps, TorusHk (K + 2) (ScalarH v.1.root)) (B : ℝ),
      (∀ v, (En v).toFunction.jet (valueIndex2 (K + 2)) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => g x v) →
      weightedNorm (rhoStar D kI.c₀ m) (G.mass law) (fun _ => 1) En ≤ B →
      profileNorm (D.eps m) K s (compField (G.mass law) g) ≤
        ENNReal.ofReal (C * D.eps (m - 1) ^ (-(q * iterZ α q s K)) * B)

/-- **The error profile**: from the weighted `H^{K+2}` norm at the radius `ρ_⋆` to the profile norm at the wavelength `e`, closed upward in `C`. -/
def PassageErrorProfileStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc : ℝ), 3 ≤ K → 0 < Pacc →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ → Pacc + q * iterZ α q s K + 4 < Q / 2 →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
    ∀ L : ℕ, IsPassageOrders α q s K Pacc σ₀ L N p nk Naux →
      IsCascadeWidths α q lamE a σ (succDstar D₀ N p H) →
    ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ (C₀ : ℝ) (mStar : ℕ), ∀ C : ℝ, C₀ ≤ C →
    PassageErrorProfileData α s q ζ Λ φ₀ hφ₀ bw K T₀ r₀ D₀ τe H J N p nk npad σ₀ sX sZ Ce kS kI CI
      Cw j₀ C mStar

/-- **A classical representative from a higher Sobolev lift** (Sobolev embedding in dimension two,
`hilbert_classicalRep_exists`). Special cases: an empty family; `k = 0`, `n = 2`. -/
def SmoothRepOfHigherStatement : Prop :=
  ∀ {S : Finset Comp} (k n : ℕ), k + 2 ≤ n →
    ∀ (X : ∀ v : CompIn S, TorusHk 0 (ScalarH v.1.root))
      (Xn : ∀ v : CompIn S, TorusHk n (ScalarH v.1.root)),
      (∀ v, truncateTorusHk (Nat.zero_le n) (Xn v) = X v) →
      ∃ a : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root, IsSmoothRep X a k

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The profile proposition of one passage with the outputs of the other ingredients as
hypotheses**.

`PassageProfileClausesStatement` is the profile proposition with, as hypotheses, four facts that
the proof needs and that the assembly of `iteration_passage` has at the pair: the readout norm
with its constant `C_n`, for every time of the window a lift of `U(t)` of order `K + N + 2p + 4`
(molecular buffer) and a lift of `Y(t)` of order `N_aux` of marked weighted norm `≤ C_r A` at
the radius `rhoEnh` (regenerated solution), and the jets `PassageJetClauses` with the constant
`C_j`. The families `U`, `Y` are arbitrary time-dependent `L²` families with these lifts; no
equation enters.

The statement is `∀ C_n C_r C_j, 0 ≤ C_r → 0 ≤ C_j → ∃ C₀ m_*, ∀ C ≥ C₀`. It follows from the
ingredient statements above (`passageProfileClauses_of_ingredients`).

Special cases: `A = 0` (the lifts of `Y` vanish, the error vanishes by the jets; every bound is
`0 ≤ 0` or homogeneous); empty families; the constants come before the data. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.IterationPassage.Passage

/-- Data part of `PassageProfileClausesStatement`. -/
def PassageProfileClausesData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (bw : ℝ) (K : ℕ) (Pacc Q T₀ : ℝ) (r₀ D₀ : ℕ) (τe : ℝ)
    (H J N p nk Naux npad : ℕ) (σ₀ : ℝ) (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ)
    (j₀ : ℕ) (Cn Cr Cj C : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (tp A : ℝ), s₀ ≤ tp → 0 ≤ A →
    ∀ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk 0 (ScalarH v.1.root)),
      ‖readoutCLM m (D.eps (m - 1)) (succEta0 α q s) (G.mass law) ((G'.retained m H J).mass law)‖ ≤
        1 + Cn * D.eps (m - 1) ^ (5 * succEta0 α q s / 4) →
      (∀ t ∈ Set.Icc tp tf, ∃ Un : ∀ v : CompIn G.comps,
        TorusHk (K + N + 2 * p + 4) (ScalarH v.1.root),
        ∀ v, truncateTorusHk (Nat.zero_le _) (Un v) = U v t) →
      (∀ t ∈ Set.Icc tp tf, ∃ Yn : ∀ v : CompIn (G'.retained m H J).comps,
        TorusHk Naux (ScalarH v.1.root),
        (∀ v, truncateTorusHk (Nat.zero_le _) (Yn v) = Y v t) ∧
        weightedNorm (rhoEnh D kI.cr m) ((G'.retained m H J).mass law) ((G'.retained m H J).marker law) Yn ≤ Cr * A) →
      (∀ (aU : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root)
          (aY : ℝ → Vec 2 → ∀ v : CompIn (G'.retained m H J).comps, ScalarH v.1.root),
        (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => U v t) (aU t) (K + N + 2 * p + 2)) →
        (∀ t ∈ Set.Icc tp tf, IsSmoothRep (fun v => Y v t) (aY t) (K + N + 2 * p + 2)) →
        ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)),
          IsPassageLift G m N (succSchedR r₀ J H) sX sZ CcT →
          PassageJetClauses law G (G'.retained m H J) m p N (succSchedR r₀ J H) K (succEta0 α q s) Q Cj
            kI.c₀ A tp tf CcT aU aY) →
      PassageClauses D law G (G'.retained m H J) m p N (succSchedR r₀ J H) sX sZ K s (succEta0 α q s)
        (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc C A tp tf φ₀ (freshK (m - 1)) U Y

/-- **The exact profile proposition of one passage** from the lifts, the jets
and the readout norm, closed upward in `C`. -/
def PassageProfileClausesStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc : ℝ), 3 ≤ K → 0 < Pacc →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ → Pacc + q * iterZ α q s K + 4 < Q / 2 →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
    ∀ L : ℕ, IsPassageOrders α q s K Pacc σ₀ L N p nk Naux →
      IsCascadeWidths α q lamE a σ (succDstar D₀ N p H) →
    ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ Cn Cr Cj : ℝ, 0 ≤ Cr → 0 ≤ Cj → ∃ (C₀ : ℝ) (mStar : ℕ), ∀ C : ℝ, C₀ ≤ C →
    PassageProfileClausesData α s q ζ Λ φ₀ hφ₀ bw K Pacc Q T₀ r₀ D₀ τe H J N p nk Naux npad σ₀ sX
      sZ Ce kS kI CI Cw j₀ Cn Cr Cj C mStar

end AVRegularity.IterationPassage.Passage
end
end
end
