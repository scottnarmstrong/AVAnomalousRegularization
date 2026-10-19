-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Iteration.CascadeStatement
import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
import AVRegularity.Readout.RepresentationEstimates
import AVRegularity.Construction.Preservation.Buffer.KernelMaterialIncrement
import AVRegularity.IterationPassage.Cascade.Recursion
import AVRegularity.Construction.EntryScales.TerminalCore
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.IterationPassage.Cascade

/-! **The representation recursion of the cascade and its summation, abstractly**.


* `timeRep_atTime_map_append`: the recursion step `rep j = (rep (j-1)).map R ++ profiles` of
  `CascadeOutput`, at one time, is the copied representation with the profiles appended.
* `cascade_rep_recursion`: for abstract component spaces `H j`, constant maps `R j : H j → H (j+1)`
  and a step hypothesis "a representation of `V j t` at `e j` gives a representation of
  `V (j+1) t` at `e (j+1)` with size `≤ (1 + g_{j+1})X + c_{j+1}`": `rep n` is a representation of
  `V n t` and `X_n ≤ exp(∑ g_j)(X_{m₀} + ∑ c_j)`. The recurrence is summed in `ℝ≥0∞`
  (`1 + g ≤ exp g`).

The degenerate cases are included: `n = m₀` (`X ≤ 1·(X + 0)`); `n = m₀ + 1` (one step). -/

/-- The recursion step of `CascadeOutput` at one time is the appended representation. -/
theorem timeRep_atTime_map_append {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H'] (R : H →L[ℝ] H') (r : TimeRep H)
    (l : List ((ℝ → Vec 2 → H') × ℝ)) (t : ℝ) :
    ((r.map R).append l).atTime t =
      ⟨((r.atTime t).map R).base,
        ((r.atTime t).map R).profiles ++ l.map fun q => (q.1 t, q.2)⟩ := by
  simp only [TimeRep.atTime, TimeRep.map, TimeRep.append, Representation.map, List.map_append,
    List.map_map]
  rfl

/-- The representation recursion and its summation, for abstract component spaces. -/
theorem cascade_rep_recursion {H : ℕ → Type} [∀ j, NormedAddCommGroup (H j)]
    [∀ j, NormedSpace ℝ (H j)] (s : ℝ) (K m₀ n : ℕ) (hmn : m₀ ≤ n) (e : ℕ → ℝ) (I : Set ℝ)
    (R : ∀ j, H j →L[ℝ] H (j + 1)) (prof : ∀ j, List ((ℝ → Vec 2 → H (j + 1)) × ℝ))
    (rep : ∀ j, TimeRep (H j)) (V : ∀ j, ℝ → Vec 2 → H j) (g c : ℕ → ℝ)
    (hg : ∀ j, 0 ≤ g j) (hc : ∀ j, 0 ≤ c j)
    (hbase : ∀ t ∈ I, IsRepresentationAt (e m₀) K ((rep m₀).atTime t) ∧
      ((rep m₀).atTime t).value = V m₀ t)
    (hrec : ∀ j, m₀ ≤ j → j < n → rep (j + 1) = ((rep j).map (R j)).append (prof j))
    (hstep : ∀ j, m₀ ≤ j → j < n → ∀ t ∈ I, ∀ rY : Representation (H j),
      IsRepresentationAt (e j) K rY → rY.value = V j t →
      IsRepresentationAt (e (j + 1)) K
          ⟨(rY.map (R j)).base, (rY.map (R j)).profiles ++ (prof j).map fun q => (q.1 t, q.2)⟩ ∧
        (⟨(rY.map (R j)).base, (rY.map (R j)).profiles ++ (prof j).map fun q => (q.1 t, q.2)⟩ :
          Representation (H (j + 1))).value = V (j + 1) t ∧
        representedSize s K (e (j + 1))
            ⟨(rY.map (R j)).base, (rY.map (R j)).profiles ++ (prof j).map fun q => (q.1 t, q.2)⟩ ≤
          ENNReal.ofReal (1 + g (j + 1)) * representedSize s K (e j) rY +
            ENNReal.ofReal (c (j + 1))) :
    ∀ t ∈ I, IsRepresentationAt (e n) K ((rep n).atTime t) ∧
      ((rep n).atTime t).value = V n t ∧
      representedSize s K (e n) ((rep n).atTime t) ≤
        ENNReal.ofReal (Real.exp (∑ j ∈ Finset.Ioc m₀ n, g j)) *
          (representedSize s K (e m₀) ((rep m₀).atTime t) +
            ENNReal.ofReal (∑ j ∈ Finset.Ioc m₀ n, c j)) := by
  intro t ht
  induction n, hmn using Nat.le_induction with
  | base =>
    refine ⟨(hbase t ht).1, (hbase t ht).2, ?_⟩
    simp
  | succ k hk ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun j hj hjk => hrec j hj (Nat.lt_succ_of_lt hjk))
      (fun j hj hjk => hstep j hj (Nat.lt_succ_of_lt hjk))
    obtain ⟨s1, s2, s3⟩ := hstep k hk (Nat.lt_succ_self k) t ht ((rep k).atTime t) h1 h2
    rw [hrec k hk (Nat.lt_succ_self k), timeRep_atTime_map_append]
    refine ⟨s1, s2, s3.trans ?_⟩
    have hS : ∑ j ∈ Finset.Ioc m₀ (k + 1), g j = (∑ j ∈ Finset.Ioc m₀ k, g j) + g (k + 1) :=
      Finset.sum_Ioc_succ_top hk g
    have hT : ∑ j ∈ Finset.Ioc m₀ (k + 1), c j = (∑ j ∈ Finset.Ioc m₀ k, c j) + c (k + 1) :=
      Finset.sum_Ioc_succ_top hk c
    have hS0 : 0 ≤ ∑ j ∈ Finset.Ioc m₀ k, g j := Finset.sum_nonneg fun j _ => hg j
    have hT0 : 0 ≤ ∑ j ∈ Finset.Ioc m₀ k, c j := Finset.sum_nonneg fun j _ => hc j
    have hge : 1 + g (k + 1) ≤ Real.exp (g (k + 1)) := by
      linarith [Real.add_one_le_exp (g (k + 1))]
    have h1e : 1 ≤ Real.exp (∑ j ∈ Finset.Ioc m₀ k, g j) * Real.exp (g (k + 1)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (add_nonneg hS0 (hg _))
    rw [hS, hT, Real.exp_add, ENNReal.ofReal_add hT0 (hc _), ← add_assoc, mul_add]
    refine add_le_add ((mul_le_mul' le_rfl h3).trans ?_)
      (le_mul_of_one_le_left' (ENNReal.one_le_ofReal.mpr h1e))
    rw [← mul_assoc, ← ENNReal.ofReal_mul (add_nonneg zero_le_one (hg _))]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hge (Real.exp_pos _).le

/-! **Monotonicity of the passage certificate, the stored amplitude, the lift**.


The cascade applies the output of each passage, which holds with the passage constant `C_pass`, at
the references `a_j = ampRef D C_a Q n ‖f‖ j` of the amplitude theorem, and raises the constant and
the amplitude to the cascade constant `C` and `ampRef D C Q n ‖f‖ j` only at the end (the
internal estimates must not run at the final constant, which is of size
`ε_{m₀}^{-Z}`). Hence the monotonicity is in both variables.

* `passageDatum_mono`: `PassageDatum` is monotone in `(C, A)` for `C ≤ C'`, `0 ≤ C'`,
  `0 ≤ A ≤ A'`, `0 ≤ ε_{m-1}`.
* `passageDatum_exists_lift`: lift coefficients of the passage exist (they are part of the
  comparison clause).
* `ampRef_nonneg`, `ampRef_mono`: the references `A_n = A₀`,
  `A_{j-1} = [1 + C(ε_{j-1}^Q + ε_{j-1}^δ)]A_j` for `1 ≤ j ≤ n` are nonnegative and monotone
  in `C ≥ 0`.

The degenerate cases are included: `A = A' = 0` (every bound is `0 ≤ 0`); `C = C'`, `A = A'`
(identity); `C < 0 ≤ C'` (covered); `j = n` (the product over `(n-1, n]` has one factor); an empty
family. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The reference is nonnegative. -/
theorem ampRef_nonneg (D : OCData) (C Q : ℝ) (n : ℕ) (A₀ : ℝ) (j : ℕ) (hC : 0 ≤ C) (hA : 0 ≤ A₀)
    (hε : ∀ k, 0 ≤ D.eps k) : 0 ≤ ampRef D C Q n A₀ j :=
  mul_nonneg hA (Finset.prod_nonneg fun _ _ => add_nonneg zero_le_one (mul_nonneg hC
    (add_nonneg (Real.rpow_nonneg (hε _) _) (Real.rpow_nonneg (hε _) _))))

/-- The reference is monotone in its constant. -/
theorem ampRef_mono (D : OCData) (C C' Q : ℝ) (n : ℕ) (A₀ : ℝ) (j : ℕ) (hC0 : 0 ≤ C)
    (hC : C ≤ C') (hA : 0 ≤ A₀) (hε : ∀ k, 0 ≤ D.eps k) :
    ampRef D C Q n A₀ j ≤ ampRef D C' Q n A₀ j := by
  unfold ampRef
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun k _ => ?_) (fun k _ => ?_)) hA
  · exact add_nonneg zero_le_one (mul_nonneg hC0
      (add_nonneg (Real.rpow_nonneg (hε _) _) (Real.rpow_nonneg (hε _) _)))
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hC
      (add_nonneg (Real.rpow_nonneg (hε _) _) (Real.rpow_nonneg (hε _) _)))

/-- `PassageDatum` is monotone in its constant and in its amplitude. -/
theorem passageDatum_mono (law : BirthLaw) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (G Gr : GenStage D ScalarH Dm b j₀) (m p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q C C' cr c₀ A A' s₀ tp tf : ℝ) (Sr : KernelSpec) {Nout : ℕ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (hC : C ≤ C') (hC' : 0 ≤ C') (hA0 : 0 ≤ A) (hA : A ≤ A') (hE : 0 ≤ D.eps (m - 1))
    (h : PassageDatum law P seedK freshK φ₀ hφ₀ G Gr m p N depth sX sZ K Naux s η₀ mu wexp Pacc Q
      C cr c₀ A s₀ tp tf Sr Preg f U Y) :
    PassageDatum law P seedK freshK φ₀ hφ₀ G Gr m p N depth sX sZ K Naux s η₀ mu wexp Pacc Q
      C' cr c₀ A' s₀ tp tf Sr Preg f U Y := by
  have hA0' : 0 ≤ A' := hA0.trans hA
  have hmul : ∀ x : ℝ, 0 ≤ x → C * x * A ≤ C' * x * A' := fun x hx =>
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hx) hA0).trans
      (mul_le_mul_of_nonneg_left hA (mul_nonneg hC' hx))
  have hCA : C * A ≤ C' * A' := by simpa only [mul_one] using hmul 1 zero_le_one
  have hx : 0 ≤ D.eps (m - 1) ^ Q + D.eps (m - 1) ^ ocDelta D.α D.q :=
    add_nonneg (Real.rpow_nonneg hE _) (Real.rpow_nonneg hE _)
  obtain ⟨h1, ⟨YN0, YN, YNw, YNk, htr, hsol, htrunc, hpt, hse, hcmp⟩, h3, h4⟩ := h
  refine ⟨fun t ht => ?_, ⟨YN0, YN, YNw, YNk, htr, hsol, htrunc,
    fun t ht => (hpt t ht).trans hCA, hse.trans (ENNReal.ofReal_le_ofReal hCA),
    Construction.Preservation.Assembly.comparisonClauses_mono (h := hcmp)
      (hres := hmul _ (Real.rpow_nonneg hE _)) (he := hmul _ (Real.rpow_nonneg hE _))⟩, ?_, ?_⟩
  · refine (h1 t ht).trans ?_
    exact (mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right hC hx))
      hA0).trans (mul_le_mul_of_nonneg_left hA
        (add_nonneg zero_le_one (mul_nonneg hC' hx)))
  · refine ⟨h3.1, fun aU aY haU haY CcT hCcT t ht => ?_⟩
    obtain ⟨p0, p1, p2, prec⟩ := h3.2 aU aY haU haY CcT hCcT t ht
    refine ⟨p0.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hE _))) le_rfl),
      p1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hE _))) le_rfl),
      p2.trans (ENNReal.ofReal_le_ofReal (hmul _ (Real.rpow_nonneg hE _))),
      fun rY hrY hval => ?_⟩
    obtain ⟨r1, r2, r3⟩ := prec rY hrY hval
    refine ⟨r1, r2, r3.trans (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hC (add_nonneg (add_nonneg
        (Real.rpow_nonneg hE _) (Real.rpow_nonneg hE _)) (Real.rpow_nonneg hE _))))) le_rfl)
      (ENNReal.ofReal_le_ofReal (hmul _ (Real.rpow_nonneg hE _))))⟩
  · intro aU aY haU haY CcT hCcT t ht
    obtain ⟨⟨Un, Uh, hUn, hUh, hb⟩, En, hEn, hbe⟩ := h4 aU aY haU haY CcT hCcT t ht
    exact ⟨⟨Un, Uh, hUn, hUh, hb.trans hCA⟩, En, hEn,
      hbe.trans (hmul _ (Real.rpow_nonneg hE _))⟩

/-- The lift coefficients of the passage are part of `PassageDatum` (first clause of
`IsLiftedField` in `ComparisonClauses`). -/
theorem passageDatum_exists_lift (law : BirthLaw) (P : ProvParams)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (G Gr : GenStage D ScalarH Dm b j₀) (m p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q C cr c₀ A s₀ tp tf : ℝ) (Sr : KernelSpec) {Nout : ℕ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (h : PassageDatum law P seedK freshK φ₀ hφ₀ G Gr m p N depth sX sZ K Naux s η₀ mu wexp Pacc Q
      C cr c₀ A s₀ tp tf Sr Preg f U Y) :
    ∃ CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root),
      IsPassageLift G m N depth sX sZ CcT := by
  obtain ⟨-, ⟨YN0, YN, YNw, YNk, -, -, -, -, -, hcmp⟩, -, -⟩ := h
  obtain ⟨CcT, PZ, aRep, û, hlift⟩ := hcmp.1
  exact ⟨CcT, hlift.1⟩
end

/-! **Timing of a frame of the cascade**.

`cascadeFrame_timing`: for `m₀ < j ≤ n`, `s_j ≤ r_j ≤ t_p^{(j)} = s_{j-1}`, `r_j ≤ t_f` and
`t_p^{(j)} ≤ t_S + t₀`; for `m₀ ≤ j ≤ n`, `s_j ≤ t_S + t₀`. So every passage window contains
`I_* = [t_S + t₀, t_f]` and the windows increase with the level.

The degenerate case is included: `n = m₀ + 1` (`t_p^{(n)} = s_{m₀}`). -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The timing of a frame: `s_j ≤ r_j ≤ t_p^{(j)} = s_{j-1}`, `r_j ≤ t_f`, and every birth
time and preparation time is at most `t_S + t₀`. -/
theorem cascadeFrame_timing (law : BirthLaw) (P : ProvParams) (Mn : SuccMenu)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (Mnat : ℕ)
    (kI : InvConsts) (CI τe η₀ : ℝ) (Kres Tw p Nout Naux : ℕ) (Q CQ C : ℝ)
    (seed : GenStage D ScalarH Dm b j₀) (n m₀ : ℕ) (tS t₀ tf : ℝ)
    (stage ext : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ)
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root)))
    (hΛ : 1 ≤ D.Λ)
    (hframe : CascadeFrame law P Mn seedK freshK φ₀ hφ₀ Mnat kI CI τe η₀ Kres Tw p Nout Naux Q CQ
      C seed n m₀ tS t₀ tf stage ext hist st tp Preg) :
    (∀ j, m₀ < j → j ≤ n →
      st j ≤ cascadeRestart D hist st j ∧ cascadeRestart D hist st j ≤ tp j ∧
        cascadeRestart D hist st j ≤ tf ∧ tp j ≤ tS + t₀) ∧
      ∀ j, m₀ ≤ j → j ≤ n → st j ≤ tS + t₀ := by
  obtain ⟨-, -, -, hbot, -, hpass⟩ := hframe
  have hstep : ∀ j, m₀ < j → j ≤ n → st j ≤ st (j - 1) := by
    intro j hj hjn
    obtain ⟨-, -, -, hst, -, hF⟩ := hpass j hj hjn
    rw [hst]
    exact (le_max_left _ _).trans hF.1.2.1
  have hanti : ∀ j, m₀ ≤ j → j ≤ n → st j ≤ st m₀ := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact fun _ => le_rfl
    | succ k hk ih =>
      intro hkn
      exact (hstep (k + 1) (Nat.lt_succ_of_le hk) hkn).trans (ih (Nat.le_of_succ_le hkn))
  refine ⟨fun j hj hjn => ?_, fun j hj hjn => (hanti j hj hjn).trans hbot⟩
  obtain ⟨-, -, -, hst, hwin, hF⟩ := hpass j hj hjn
  have hτ := Construction.Stream.ocTauPP_pos (α := D.α) (q := D.q) (m := j) hΛ
  refine ⟨le_max_left _ _, hF.1.2.1, by linarith, ?_⟩
  rw [← hst]
  exact (hanti (j - 1) (by omega) (by omega)).trans hbot
end

end AVRegularity.IterationPassage.Cascade
end

section
namespace AVRegularity.IterationPassage.Cascade

/-! **The bottom bound, part 1: scale algebra and norm comparisons**.

* `bottom_scale_sum_le`: abstract-real scale algebra. For `0 < E ≤ 1`, `c ≥ 0`,
  `ρ ≥ (c_r/C_r) E^{1+c}` with `0 < c_r ≤ 1 ≤ C_r`:
  `∑_{j ≤ K} E^{j-s} ρ^{-j-1} ≤ (K+1) (C_r/c_r)^{K+1} E^{-(1+s+c(K+1))}`.
* `bottom_weightedNorm_le_marked`: unmarked norm is at most the marked norm for markers `≥ 1`.
* `bottom_representedSize_le`: `representedSize s K λ ⟨F, []⟩ ≤ 4 profileNorm λ K s F`.
The degenerate cases are included: `K = 0`; `c = 0`; `ρ = (c_r/C_r)E^{1+c}` (equality in the first
lemma, `j = K`). -/

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity
open scoped ENNReal

theorem bottom_scale_term_le {E ρ cr Cr c s : ℝ} {K j : ℕ} (hj : j ≤ K) (hE0 : 0 < E)
    (hE1 : E ≤ 1) (hcr0 : 0 < cr) (hCr : 1 ≤ Cr) (hcr1 : cr ≤ 1) (hc : 0 ≤ c)
    (hρ : cr / Cr * E ^ (1 + c) ≤ ρ) :
    E ^ ((j : ℝ) - s) * ρ ^ (-(j : ℝ) - 1) ≤
      (Cr / cr) ^ (K + 1) * E ^ (-(1 + s + c * ((K : ℝ) + 1))) := by
  have hCr0 : 0 < Cr := by linarith
  have hlow : 0 < cr / Cr * E ^ (1 + c) := by positivity
  have hρ0 : 0 < ρ := lt_of_lt_of_le hlow hρ
  have he : -(j : ℝ) - 1 = -((j + 1 : ℕ) : ℝ) := by push_cast; ring
  have h1 : ρ ^ (-(j : ℝ) - 1) ≤ (cr / Cr * E ^ (1 + c)) ^ (-(j : ℝ) - 1) :=
    Real.rpow_le_rpow_of_nonpos hlow hρ (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  have h2 : (cr / Cr * E ^ (1 + c)) ^ (-(j : ℝ) - 1) =
      (Cr / cr) ^ (j + 1) * E ^ (-(1 + c) * ((j : ℝ) + 1)) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hE0.le, he,
      Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_div, inv_pow, inv_inv]
    congr 2
    push_cast
    ring
  have h3 : E ^ ((j : ℝ) - s) * E ^ (-(1 + c) * ((j : ℝ) + 1)) =
      E ^ (-(1 + s + c * ((j : ℝ) + 1))) := by
    rw [← Real.rpow_add hE0]
    congr 1
    ring
  have h4 : E ^ (-(1 + s + c * ((j : ℝ) + 1))) ≤ E ^ (-(1 + s + c * ((K : ℝ) + 1))) := by
    apply Real.rpow_le_rpow_of_exponent_ge hE0 hE1
    have : (j : ℝ) ≤ K := by exact_mod_cast hj
    nlinarith
  have h5 : (Cr / cr) ^ (j + 1) ≤ (Cr / cr) ^ (K + 1) := by
    apply pow_le_pow_right₀ _ (by omega)
    rw [le_div_iff₀ hcr0]; linarith
  have hEpos : 0 < E ^ ((j : ℝ) - s) := Real.rpow_pos_of_pos hE0 _
  calc E ^ ((j : ℝ) - s) * ρ ^ (-(j : ℝ) - 1)
      ≤ E ^ ((j : ℝ) - s) * ((Cr / cr) ^ (j + 1) * E ^ (-(1 + c) * ((j : ℝ) + 1))) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hEpos.le
    _ = (Cr / cr) ^ (j + 1) * E ^ (-(1 + s + c * ((j : ℝ) + 1))) := by rw [← h3]; ring
    _ ≤ (Cr / cr) ^ (K + 1) * E ^ (-(1 + s + c * ((K : ℝ) + 1))) := by
        apply mul_le_mul h5 h4 (Real.rpow_pos_of_pos hE0 _).le (by positivity)

theorem bottom_scale_sum_le {E ρ cr Cr c s : ℝ} {K : ℕ} (hE0 : 0 < E)
    (hE1 : E ≤ 1) (hcr0 : 0 < cr) (hCr : 1 ≤ Cr) (hcr1 : cr ≤ 1) (hc : 0 ≤ c)
    (hρ : cr / Cr * E ^ (1 + c) ≤ ρ) :
    ∑ j ∈ Finset.range (K + 1), E ^ ((j : ℝ) - s) * ρ ^ (-(j : ℝ) - 1) ≤
      ((K : ℝ) + 1) * ((Cr / cr) ^ (K + 1) * E ^ (-(1 + s + c * ((K : ℝ) + 1)))) := by
  calc _ ≤ ∑ _j ∈ Finset.range (K + 1),
        (Cr / cr) ^ (K + 1) * E ^ (-(1 + s + c * ((K : ℝ) + 1))) :=
        Finset.sum_le_sum fun j hj => bottom_scale_term_le (Finset.mem_range_succ_iff.mp hj)
          hE0 hE1 hcr0 hCr hcr1 hc hρ
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

theorem bottom_weightedNorm_le_marked {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {S : Finset Comp} {k : ℕ} (ρ : ℝ) (π w : CompIn S → ℝ) (hπ : ∀ v, 0 < π v)
    (hw : ∀ v, 1 ≤ w v) (X : ∀ v : CompIn S, TorusHk k (hr v.1.root)) :
    weightedNorm ρ π (fun _ => 1) X ≤ weightedNorm ρ π w X := by
  unfold weightedNorm massNormSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun v _ => ?_)
  refine mul_le_mul_of_nonneg_right ?_ (Sobolev.factorialNormSq_nonneg ρ _)
  have h1 : (0 : ℝ) < w v ^ 2 := by have := hw v; positivity
  have h2 : π v / w v ^ 2 ≤ π v / (fun _ : CompIn S => (1 : ℝ)) v ^ 2 := by
    simp only [one_pow, div_one]
    exact div_le_self (hπ v).le (by nlinarith [hw v])
  exact inv_anti₀ (div_pos (hπ v) h1) h2

theorem bottom_representedSize_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {s lam : ℝ} {K : ℕ} (hK : 1 ≤ K) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hs₀ : 0 < s) (hs₁ : s < 1) (F : Vec 2 → H) (hF : ContDiff ℝ K F)
    (hper : AVenhance.IsZ2Periodic F) :
    representedSize s K lam (⟨F, []⟩ : Representation H) ≤ 4 * profileNorm lam K s F := by
  have h1 := Readout.profile_holder_cost hK hlam hlam1 hs₀ hs₁ F hF hper
  have h2 : profileSeminorm lam K s F ≤ profileNorm lam K s F := by
    unfold profileNorm; exact le_add_self
  unfold representedSize
  simp only [List.map_nil, List.sum_nil, add_zero]
  calc supNorm F + profileSeminorm lam K s F + holderSeminorm s F
      = (supNorm F + holderSeminorm s F) + profileSeminorm lam K s F := by ring
    _ ≤ 3 * profileNorm lam K s F + profileNorm lam K s F := add_le_add h1 h2
    _ = 4 * profileNorm lam K s F := by ring

end AVRegularity.IterationPassage.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.Cascade

/-! **Ingredients of `iteration_cascade_of_schedule`**.

The cascade is the datum-independent run (stages, successors, times and preparations)
followed, for each datum, by the families and the represented size. Both
ingredients have the prefix of the statement (`CascadeTail` up to the constants).

* `CascadeRunStatement`: above a level threshold `m_R`, for every bottom level `m₀ ≥ m_R`, the frame
  `CascadeFrame` exists, and each passage `m₀ < j ≤ n` of the run has its `PassageOutput` at one
  passage constant `C_pass`. From `iteration_passage` and `successor_exists`,
  `seed_invariant_discharge`, `cascade_wait` (the downward recursion).
* `CascadeFamiliesStatement`: for every passage constant `C_pass` and frame constants `C_Q, C_p`
  there is `m_A` such that, for every `m₀ ≥ m_A`, there is `C > 0` (it may depend on `m₀`: the
  bottom bound costs `ε_{m₀}^{-Z_K}`) with which every frame
  with those passage outputs gives `CascadeOutput` for every datum (families by existence, restart, amplitudes
  from `cascade_amplitude_product`, representation recursion, bottom bound, product).

The degenerate cases are included. `n = m₀ + 1` (one passage). An empty seed family (all families
are empty functions and the represented size is `0`). `f = 0`. The constants
`C_pass, C_Q, C_p, m_R`, then `m_A`, then `C` for the bottom level `m₀`, come before the data; `m₀`
is the maximum of the two thresholds in the assembly. -/

/-- Data part of `CascadeRunStatement`: the frame and the passage outputs of the run. -/
def CascadeRunData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw : ℝ)
    (K : ℕ) (Pacc t₀ T₀ : ℝ) (r₀ D₀ : ℕ) (τe Q : ℝ) (H J N p nk Naux Nout Kres npad sX sZ : ℕ)
    (σ₀ Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ)
    (Cpass CQ Cp : ℝ) (m₀ : ℕ) : Prop :=
  ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw),
    IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
  ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
    tS + t₀ < tf → tf - tS ≤ T₀ →
    IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
      Mnat kS seed n tS tf Ce τe r₀ D₀ →
    IsSeedPointwiseMolecular law kS seed tS tf →
    m₀ < n → n < M →
  ∃ (stage ext : ℕ → GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (hist st tp : ℕ → ℝ)
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root))),
    CascadeFrame law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
      (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seedK freshK φ₀ hφ₀ Mnat kI CI τe
      (succEta0 α q s) Kres (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card p Nout
      Naux Q CQ Cp seed n m₀ tS t₀ tf stage ext hist st tp Preg ∧
    ∀ j, m₀ < j → j ≤ n →
      PassageOutput law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        (stage j) (stage (j - 1)) j p N (succSchedR r₀ J H) sX sZ K Naux s (succEta0 α q s)
        (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc Q Cpass kI.cr kI.c₀ (cascadeRestart D hist st j)
        (tp j) tf (freshK (j - 1)) (Preg j)

/-- The tail of `CascadeRunStatement` after the lift orders. -/
def CascadeRunTail (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (c₀max : ℝ) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (bw : ℝ) (K : ℕ) (Pacc t₀ T₀ : ℝ) (r₀ D₀ : ℕ) (τe lamE σE Q : ℝ)
    (H J N p nk Lc Lf Lpr Naux Nout Kres npad sX sZ Kneed : ℕ) (σ₀ : ℝ) : Prop :=
  ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
    0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
    IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
    Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
  ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
    IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
  ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
    IsCarrierStart α q Λ bw CH Υ j₀ →
  ∃ (Cpass CQ Cp : ℝ) (mR : ℕ), ∀ m₀ : ℕ, mR ≤ m₀ →
  CascadeRunData α s q ζ Λ φ₀ hφ₀ bw K Pacc t₀ T₀ r₀ D₀ τe Q H J N p nk Naux Nout Kres npad sX sZ σ₀ Ce kS kI
      CI Cw j₀ Cpass CQ Cp m₀

/-- **The run of the cascade**: frame and passage outputs. -/
def CascadeRunStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc t₀ T₀ : ℝ), 3 ≤ K → 0 < Pacc → 0 < t₀ → t₀ < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (Q : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ) (σ₀ a σ : ℝ),
      IsCascadeSchedule α s q K Pacc lamE σE D₀ Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a σ →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
      ∀ npad : ℕ, ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
      CascadeRunTail α s q ζ Λ c₀max φ₀ hφ₀ bw K Pacc t₀ T₀ r₀ D₀ τe lamE σE Q H J N p nk Lc Lf Lpr
        Naux Nout Kres npad sX sZ Kneed σ₀

/-- Data part of `CascadeFamiliesStatement`: `CascadeOutput` for every frame with its passage
outputs and every datum. -/
def CascadeFamiliesData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw : ℝ)
    (K : ℕ) (Pacc t₀ T₀ : ℝ) (r₀ D₀ : ℕ) (τe Q : ℝ) (H J N p nk Naux Nout Kres npad sX sZ : ℕ)
    (σ₀ Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ)
    (Cpass CQ Cp C : ℝ) (m₀ : ℕ) : Prop :=
  ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw),
    IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
  ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
    tS + t₀ < tf → tf - tS ≤ T₀ →
    IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
      Mnat kS seed n tS tf Ce τe r₀ D₀ →
    IsSeedPointwiseMolecular law kS seed tS tf →
    m₀ < n → n < M →
  ∀ (stage ext : ℕ → GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (hist st tp : ℕ → ℝ)
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root))),
    CascadeFrame law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
      (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seedK freshK φ₀ hφ₀ Mnat kI CI τe
      (succEta0 α q s) Kres (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card p Nout
      Naux Q CQ Cp seed n m₀ tS t₀ tf stage ext hist st tp Preg →
    (∀ j, m₀ < j → j ≤ n →
      PassageOutput law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        (stage j) (stage (j - 1)) j p N (succSchedR r₀ J H) sX sZ K Naux s (succEta0 α q s)
        (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc Q Cpass kI.cr kI.c₀ (cascadeRestart D hist st j)
        (tp j) tf (freshK (j - 1)) (Preg j)) →
    ∀ f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root),
      CascadeOutput law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        p N (succSchedR r₀ J H) sX sZ K Naux s (succEta0 α q s) (ocMuS α q s)
        (ocDelta α q - 2 * σ₀) Pacc Q C kI.cr kI.c₀ n m₀ tS t₀ tf stage hist st tp Preg f

/-- The tail of `CascadeFamiliesStatement` after the lift orders. -/
def CascadeFamiliesTail (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (c₀max : ℝ) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (bw : ℝ) (K : ℕ) (Pacc t₀ T₀ : ℝ) (r₀ D₀ : ℕ) (τe lamE σE Q : ℝ)
    (H J N p nk Lc Lf Lpr Naux Nout Kres npad sX sZ Kneed : ℕ) (σ₀ : ℝ) : Prop :=
  ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
    0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
    IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
    Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
  ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
    IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
  ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
    IsCarrierStart α q Λ bw CH Υ j₀ →
  ∀ Cpass CQ Cp : ℝ, ∃ mA : ℕ, ∀ m₀ : ℕ, mA ≤ m₀ → ∃ C : ℝ, 0 < C ∧
  CascadeFamiliesData α s q ζ Λ φ₀ hφ₀ bw K Pacc t₀ T₀ r₀ D₀ τe Q H J N p nk Naux Nout Kres npad sX sZ σ₀ Ce kS kI
      CI Cw j₀ Cpass CQ Cp C m₀

/-- **The families of the cascade** for every frame and datum. -/
def CascadeFamiliesStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc t₀ T₀ : ℝ), 3 ≤ K → 0 < Pacc → 0 < t₀ → t₀ < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (Q : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ) (σ₀ a σ : ℝ),
      IsCascadeSchedule α s q K Pacc lamE σE D₀ Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a σ →
      ∀ npad : ℕ, ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
      CascadeFamiliesTail α s q ζ Λ c₀max φ₀ hφ₀ bw K Pacc t₀ T₀ r₀ D₀ τe lamE σE Q H J N p nk Lc Lf Lpr
        Naux Nout Kres npad sX sZ Kneed σ₀

end AVRegularity.IterationPassage.Cascade
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.Cascade

/-! **Stage solutions of the cascade: restart and order-zero existence**.


* `StageSol`: a homogeneous order-zero solution of a stage at the level `m` from the time `s`, in
  the direct form of the statements (`CascadeOutput`, `PassageOutput`, `cascade_amplitude_product`),
  elaborated once.
* `stageSol_restart`: a solution from `s` is the solution restarted at any `r ≥ s` from its own
  value (`KernelEnergy.weakIdentity_restart`); no bound `r ≤ t_f` is needed, so the clause of
  `CascadeOutput` at `j = m₀`, whose window may be empty, is covered.
* `stageSol_exists`: the order-zero solution of a cascade stage with its invariant on
  `[t_A, t_f]` exists from every time `s ∈ [t_A, t_f]` and every `L²` datum
  (`nativeInvariantKernelOperator`, `stream_kernel_order_zero_exists`). Uniqueness is not used.

The degenerate cases are included. An empty family: the same proofs. `f = 0`: some solution exists.
`r > t_f`: the restart holds on the empty window. `n = m₀ + 1`: existence is used once (at the
seed). -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- A homogeneous order-zero solution of a stage at the level `m` from the time `s`, in the direct
form of the statements (`CascadeOutput`, `PassageOutput`, `cascade_amplitude_product`). -/
def StageSol (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (G : GenStage D ScalarH Dm b j₀) (m : ℕ) (s tf : ℝ)
    (Y0 : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)) : Prop :=
  G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ m) (streamVel (D.Φ m)) 0 s tf Y0
    (fun _ _ => 0) (fun _ _ => 0) U Uw Uk

/-- Restart at a later time `r ≥ s`; no bound `r ≤ t_f` is needed. -/
theorem stageSol_restart (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (G : GenStage D ScalarH Dm b j₀) (m : ℕ) (s r tf : ℝ) (hsr : s ≤ r)
    (Y0 : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root))
    (h : StageSol P seedK freshK φ₀ hφ₀ G m s tf Y0 U Uw Uk) :
    StageSol P seedK freshK φ₀ hφ₀ G m r tf (fun v => U v r) U Uw Uk := by
  have hsub : Set.Icc r tf ⊆ Set.Icc s tf := Set.Icc_subset_Icc hsr le_rfl
  have hμ : volume.restrict (Set.Icc r tf) ≤ volume.restrict (Set.Icc s tf) :=
    Measure.restrict_mono hsub le_rfl
  refine ⟨fun v => (h.1 v).mono hsub, fun v => (h.2.1 v).mono_measure hμ,
    fun v => ae_restrict_of_ae_restrict_of_subset hsub (h.2.2.1 v), fun _ => rfl,
    fun v u γ => (h.2.2.2.2.1 v u γ).mono_measure hμ,
    fun v u γ => ae_restrict_of_ae_restrict_of_subset hsub (h.2.2.2.2.2.1 v u γ), ?_⟩
  intro v t ht φ
  have hr' : r ∈ Set.Icc s tf := ⟨hsr, ht.1.trans ht.2⟩
  exact KernelEnergy.weakIdentity_restart (volume.restrict unitCube) (D.κ m) s r t hsr ht.1
    _ _ _ _ _ _ _ _ _ _ (h.2.2.2.2.2.2 v t (hsub ht) φ) (h.2.2.2.2.2.2 v r hr' φ)

/-- Existence of the order-zero solution of a cascade stage with its invariant on
`[t_A, t_f]`, from every time `s ∈ [t_A, t_f]` and every `L²` datum. -/
theorem stageSol_exists (law : BirthLaw) (P : ProvParams) (Mn : SuccMenu)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (Mnat : ℕ)
    (kI : InvConsts) (tA tf S θ : ℝ) (seed G : GenStage D ScalarH Dm b j₀) (m : ℕ)
    (hlev : G.level = m)
    (hI : IsStageInvariant law P seedK freshK φ₀ hφ₀ Mnat kI tA tf S θ G)
    (hseed : ∀ v : CompIn seed.comps, v.1.births = [])
    (hc : IsCascadeStage D P Mn seed G) (hk : kI.Hprod = kI.G0 + Mn.H + 1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hi : 1 ≤ m) (hj : j₀ ≤ m) (hterm : m ≤ D.term)
    (hb : 0 < b) (hκ : 0 < D.κ m) (hc₀ : 0 < kI.c₀) (hc₀1 : kI.c₀ ≤ 1) (hD : 2 ≤ Dm)
    (hθ : θ ≤ 1 / 8) (s : ℝ) (hs : tA ≤ s) (hst : s ≤ tf)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) :
    ∃ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
      StageSol P seedK freshK φ₀ hφ₀ G m s tf f U Uw Uk := by
  subst hlev
  have he (i : ℕ) : 0 < D.eps i := (Scales.epsilon_basic (m := i) hq hΛ).1
  have hνeq : D.kap G.level = D.κ G.level := by rw [OCData.kap, min_eq_left hterm]
  have hν : 0 < D.kap G.level := hνeq ▸ hκ
  have hρ : 0 < rhoStar D kI.c₀ G.level :=
    mul_pos hc₀ (lt_min (he _) (Real.sqrt_pos.mpr
      (div_pos hκ (Real.rpow_pos_of_pos (he _) _))))
  have hρε : rhoStar D kI.c₀ G.level ≤ D.eps (G.level - 1) :=
    ((mul_le_mul_of_nonneg_left (min_le_left _ _) hc₀.le).trans
      (mul_le_of_le_one_left (he _).le hc₀1)).trans
      (EntryScales.epsilon_antitone hq hΛ (Nat.sub_le _ _))
  let P₀ := Construction.Preservation.Buffer.nativeInvariantKernelOperator law P Mn seedK freshK
    φ₀ hφ₀ Mnat kI tA tf S θ seed G hI hseed hc hk hq hΛ hi hj hb (he _) (hs.trans hst) hν hρ hρε
    hD hθ 0 (Nat.zero_le _) (fun _ => 1) (Or.inl rfl)
  let P₁ := Construction.Preservation.Buffer.kernelOperator_time_restrict P₀
    (Set.Icc_subset_Icc hs le_rfl) hst
  obtain ⟨U, Uw, Uk, hsol⟩ :=
    Construction.Preservation.Buffer.TorusKernelOperator.stream_kernel_order_zero_exists P₁
      (D.hΦ G.level) f
  refine ⟨U, Uw, Uk, ?_⟩
  unfold StageSol
  rw [← hνeq]
  exact hsol

end AVRegularity.IterationPassage.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.IterationPassage.Cascade

/-! **The output of a passage for one datum, with named predicates**.

* `PassageOutputFor`: the conclusion of `PassageOutput` for one datum `f`, amplitude `A` and
  incoming solution `U`: a retained solution exists, and every retained solution satisfies
  `PassageDatum`.
* `passageOutputFor_restart`: `PassageOutput` applies to a solution from an earlier time `s ≤ s₀`,
  restarted at the preparation start `s₀`, with the datum `U(s₀)` and any `A ≥ ‖d U(s₀)‖_π`.

The named predicates `StageSol` and `PassageOutputFor` keep the statement short.

The degenerate cases are included: an empty family; `A` equal to the norm itself. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The conclusion of `PassageOutput` for one datum, amplitude and incoming solution. -/
def PassageOutputFor (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth sX sZ K Naux : ℕ) (s η₀ mu wexp Pacc Q C cr c₀ s₀ tp tf : ℝ) (Sr : KernelSpec)
    {Nout : ℕ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) (A : ℝ)
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root)) : Prop :=
  (∃ (Y0' : ∀ v' : CompIn Gr.comps, TorusHk 0 (ScalarH v'.1.root))
      (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
    IsRetainedTrace G Gr m p tp (Preg f) Y0' ∧ StageSol P seedK freshK φ₀ hφ₀ Gr (m - 1) tp tf
      Y0' Y Yw Yk) ∧
  ∀ (Y0' : ∀ v' : CompIn Gr.comps, TorusHk 0 (ScalarH v'.1.root))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
    IsRetainedTrace G Gr m p tp (Preg f) Y0' →
    StageSol P seedK freshK φ₀ hφ₀ Gr (m - 1) tp tf Y0' Y Yw Yk →
    PassageDatum law P seedK freshK φ₀ hφ₀ G Gr m p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C
      cr c₀ A s₀ tp tf Sr Preg f U Y

/-- Clause (iii) with named predicates. -/
theorem passageOutputFor_restart (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G Gr : GenStage D ScalarH Dm b j₀)
    (m p N depth sX sZ K Naux : ℕ) (s η₀ mu wexp Pacc Q C cr c₀ s₀ tp tf : ℝ) (Sr : KernelSpec)
    {Nout : ℕ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root)))
    (hout : PassageOutput law P seedK freshK φ₀ hφ₀ G Gr m p N depth sX sZ K Naux s η₀ mu wexp
      Pacc Q C cr c₀ s₀ tp tf Sr Preg)
    (st : ℝ) (hs : st ≤ s₀) (Y0 : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root))
    (hsol : StageSol P seedK freshK φ₀ hφ₀ G m st tf Y0 U Uw Uk)
    (A : ℝ) (hA : weightedNorm 1 (G.mass law) (G.marker law) (fun v => U v s₀) ≤ A) :
    PassageOutputFor law P seedK freshK φ₀ hφ₀ G Gr m p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C
      cr c₀ s₀ tp tf Sr Preg (fun v => U v s₀) A U :=
  hout (fun v => U v s₀) A hA U Uw Uk
    (stageSol_restart P seedK freshK φ₀ hφ₀ G m st s₀ tf hs Y0 U Uw Uk hsol)
end

/-! **The families of a datum along a run of the cascade**.

* `StageFam G`: the four families `(Y0, U, Uw, Uk)` of an order-zero solution of the stage `G`.
* `cascade_families_exist`: from an order-zero solution of the top stage from `f` at `s_n`, the
  outputs of the passages `m₀ < j ≤ n`, and `s_{j-1} = t_p^{(j)}`: families `X j` for all levels
  with `(X n).Y0 = f`, each a solution of `stage j` from `s_j`, and `(X (j-1)).Y0` the retained
  trace of passage `j` applied to `U_j(r_j)`. The recursion is `exists_downward_family`; the step
  restarts the solution at `r_j ≥ s_j` and takes a retained solution from `PassageOutput`, at the
  amplitude `A :=` the marked norm of `U_j(r_j)` itself. No bound enters here.

The degenerate cases are included: `n = m₀ + 1` (one step); `n = m₀` (the top solution alone); an
empty family. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The four families of an order-zero solution of a stage. -/
structure StageFam (G : GenStage D ScalarH Dm b j₀) where
  /-- The datum. -/
  Y0 : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)
  /-- The solution. -/
  U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root)
  /-- Its gradient family. -/
  Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root)
  /-- Its kernel family. -/
  Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)

/-- **The families of a datum along a run.** -/
theorem cascade_families_exist (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q C cr c₀ : ℝ) (n m₀ : ℕ) (hm : m₀ ≤ n) (tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ) {Nout : ℕ}
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root)))
    (hst : ∀ j, m₀ < j → j ≤ n → st (j - 1) = tp j)
    (hpass : ∀ j, m₀ < j → j ≤ n →
      PassageOutput law P seedK freshK φ₀ hφ₀ (stage j) (stage (j - 1)) j p N depth sX sZ K Naux
        s η₀ mu wexp Pacc Q C cr c₀ (cascadeRestart D hist st j) (tp j) tf (freshK (j - 1))
        (Preg j))
    (top : StageFam (stage n))
    (htop : StageSol P seedK freshK φ₀ hφ₀ (stage n) n (st n) tf top.Y0 top.U top.Uw top.Uk) :
    ∃ X : (j : ℕ) → StageFam (stage j), X n = top ∧
      (∀ j, m₀ ≤ j → j ≤ n →
        StageSol P seedK freshK φ₀ hφ₀ (stage j) j (st j) tf (X j).Y0 (X j).U (X j).Uw (X j).Uk) ∧
      ∀ j, m₀ < j → j ≤ n →
        IsRetainedTrace (stage j) (stage (j - 1)) j p (tp j)
          (Preg j (fun v => (X j).U v (cascadeRestart D hist st j))) (X (j - 1)).Y0 := by
  classical
  have h := exists_downward_family (T := fun j => StageFam (stage j)) n
    (fun j F => StageSol P seedK freshK φ₀ hφ₀ (stage j) j (st j) tf F.Y0 F.U F.Uw F.Uk)
    (fun j F F' => IsRetainedTrace (stage j) (stage (j - 1)) j p (tp j)
      (Preg j (fun v => F.U v (cascadeRestart D hist st j))) F'.Y0)
    (Function.update (fun j => (⟨0, 0, 0, 0⟩ : StageFam (stage j))) n top)
    (by rw [Function.update_self]; exact htop) m₀ hm
    (by
      intro j hj hjn x hx
      obtain ⟨Y0', Y, Yw, Yk, htr, hsol⟩ := (passageOutputFor_restart law P seedK freshK φ₀ hφ₀
        (stage j) (stage (j - 1)) j p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C cr c₀
        (cascadeRestart D hist st j) (tp j) tf (freshK (j - 1)) (Preg j) (hpass j hj hjn) (st j)
        (le_max_left _ _) x.Y0 x.U x.Uw x.Uk hx _ le_rfl).1
      refine ⟨⟨Y0', Y, Yw, Yk⟩, htr, ?_⟩
      rw [hst j hj hjn]
      exact hsol)
  rw [Function.update_self] at h
  exact h
end

/-! **The data of a datum along a run of the cascade**.

Named hypotheses, elaborated once:

* `AmplitudeAt`: the conclusion of `cascade_amplitude_product` at the data of a run,
  for its constant `C_a`: for all families of a datum, the marked amplitudes are at most
  `a_j = ampRef D C_a Q n ‖f‖ j` on `[s_j, t_f]`, and `a_j ≤ C_a‖f‖`.
* `BottomAt`: the bottom bound (`CascadeBottomData` at the passage `m₀ + 1`).

Lemmas, for families `X j` of a run:

* `cascade_passage_datum`: `PassageDatum` of every passage at a constant `C₁ ≥ C_pass`, `C₁ ≥ 0`
  and amplitudes `a_j` bounding the marked norms on `[s_j, t_f]`: the output of the passage at the
  solution restarted at `r_j`, with `A := a_j`, then `passageDatum_mono`. `C₁` and `a_j` do not depend on the bottom level; the cascade constant enters only at the end.
* `cascade_lifts_exist`, `cascade_reps_exist`: lift coefficients and classical representatives for
  every level, by choice: the representative of `U_j` is the one of the outgoing solution of the
  passage `j + 1` (on `[s_j, t_f]`), and for `j = n` the one of the incoming solution of the
  passage `n` (on `[t_p^{(n)}, t_f]`); the windows of the passages are nested.

The degenerate cases are included: `n = m₀ + 1` (one passage; the bottom is its outgoing solution);
an empty family; `f = 0` (`a_j = 0`). -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The amplitude theorem at the data of a run, with its constant `C_a`. -/
def AmplitudeAt (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (p : ℕ) (Q Ca : ℝ) (n m₀ : ℕ) (tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ) {Nout : ℕ}
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root))) : Prop :=
  ∀ (f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root))
    (U : (j : ℕ) → ∀ v : CompIn (stage j).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : (j : ℕ) → ∀ v : CompIn (stage j).comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : (j : ℕ) → ∀ v u (_ : (stage j).fam.Γ v u), ℝ →
      TorusHk (0 + Dm - 1) (ScalarH u.1.root))
    (Y0 : (j : ℕ) → ∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)),
    Y0 n = f →
    (∀ j, m₀ ≤ j → j ≤ n →
      StageSol P seedK freshK φ₀ hφ₀ (stage j) j (st j) tf (Y0 j) (U j) (Uw j) (Uk j)) →
    (∀ j, m₀ < j → j ≤ n →
      IsRetainedTrace (stage j) (stage (j - 1)) j p (tp j)
        (Preg j (fun v => U j v (cascadeRestart D hist st j))) (Y0 (j - 1))) →
    ∀ j, m₀ ≤ j → j ≤ n →
      (∀ t ∈ Set.Icc (st j) tf,
        weightedNorm 1 ((stage j).mass law) ((stage j).marker law) (fun v => U j v t) ≤
          ampRef D Ca Q n (weightedNorm 1 ((stage n).mass law) (fun _ => 1) f) j) ∧
      ampRef D Ca Q n (weightedNorm 1 ((stage n).mass law) (fun _ => 1) f) j ≤
        Ca * weightedNorm 1 ((stage n).mass law) (fun _ => 1) f

/-- The bottom bound at the stage `G` (the outgoing stage of the passage `m → m - 1`), for
families of order `n`: size `≤ C_b E^{-Z} B`. -/
def BottomAt (law : BirthLaw) (G : GenStage D ScalarH Dm b j₀) (m K n : ℕ) (s cr Cb E Z : ℝ) :
    Prop :=
  ∀ (Yn : ∀ v : CompIn G.comps, TorusHk n (ScalarH v.1.root))
    (a : Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root) (B : ℝ),
    ContDiff ℝ (K : ℕ) a → IsZ2Periodic a →
    (∀ v, (Yn v).toFunction.jet (valueIndex2 n) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => a x v) →
    weightedNorm (rhoEnh D cr m) (G.mass law) (G.marker law) Yn ≤ B →
    representedSize s K E
        (⟨compField (G.mass law) a, []⟩ : Representation (CompSpace G.comps)) ≤
      ENNReal.ofReal (Cb * E ^ (-Z) * B)

/-- **The certificate of every passage at an intermediate constant and amplitudes.** -/
theorem cascade_passage_datum (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q Cpass C₁ cr c₀ : ℝ) (n m₀ : ℕ) (tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ) {Nout : ℕ}
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root)))
    (X : (j : ℕ) → StageFam (stage j)) (a : ℕ → ℝ) (hC : Cpass ≤ C₁) (hC₁ : 0 ≤ C₁)
    (ha : ∀ j, 0 ≤ a j) (hε : ∀ k, 0 ≤ D.eps k)
    (hst : ∀ j, m₀ < j → j ≤ n → st (j - 1) = tp j)
    (hr : ∀ j, m₀ < j → j ≤ n → cascadeRestart D hist st j ≤ tf)
    (hpass : ∀ j, m₀ < j → j ≤ n →
      PassageOutput law P seedK freshK φ₀ hφ₀ (stage j) (stage (j - 1)) j p N depth sX sZ K Naux
        s η₀ mu wexp Pacc Q Cpass cr c₀ (cascadeRestart D hist st j) (tp j) tf (freshK (j - 1))
        (Preg j))
    (hsol : ∀ j, m₀ ≤ j → j ≤ n →
      StageSol P seedK freshK φ₀ hφ₀ (stage j) j (st j) tf (X j).Y0 (X j).U (X j).Uw (X j).Uk)
    (htr : ∀ j, m₀ < j → j ≤ n →
      IsRetainedTrace (stage j) (stage (j - 1)) j p (tp j)
        (Preg j (fun v => (X j).U v (cascadeRestart D hist st j))) (X (j - 1)).Y0)
    (hamp : ∀ j, m₀ ≤ j → j ≤ n → ∀ t ∈ Set.Icc (st j) tf,
      weightedNorm 1 ((stage j).mass law) ((stage j).marker law) (fun v => (X j).U v t) ≤ a j) :
    ∀ j, m₀ < j → j ≤ n →
      PassageDatum law P seedK freshK φ₀ hφ₀ (stage j) (stage (j - 1)) j p N depth sX sZ K Naux
        s η₀ mu wexp Pacc Q C₁ cr c₀ (a j) (cascadeRestart D hist st j) (tp j) tf (freshK (j - 1))
        (Preg j) (fun v => (X j).U v (cascadeRestart D hist st j)) (X j).U (X (j - 1)).U := by
  intro j hj hjn
  have hsol' : StageSol P seedK freshK φ₀ hφ₀ (stage (j - 1)) (j - 1) (tp j) tf (X (j - 1)).Y0
      (X (j - 1)).U (X (j - 1)).Uw (X (j - 1)).Uk := by
    rw [← hst j hj hjn]
    exact hsol (j - 1) (by omega) (by omega)
  have hout := passageOutputFor_restart law P seedK freshK φ₀ hφ₀ (stage j) (stage (j - 1)) j p N
    depth sX sZ K Naux s η₀ mu wexp Pacc Q Cpass cr c₀ (cascadeRestart D hist st j) (tp j) tf
    (freshK (j - 1)) (Preg j) (hpass j hj hjn) (st j) (le_max_left _ _) (X j).Y0 (X j).U (X j).Uw
    (X j).Uk (hsol j hj.le hjn) (a j)
    (hamp j hj.le hjn _ ⟨le_max_left _ _, hr j hj hjn⟩)
  exact passageDatum_mono law P seedK freshK φ₀ hφ₀ (stage j) (stage (j - 1)) j p N depth sX sZ K
    Naux s η₀ mu wexp Pacc Q Cpass C₁ cr c₀ (a j) (a j) (cascadeRestart D hist st j) (tp j) tf
    (freshK (j - 1)) (Preg j) _ _ _ hC hC₁ (ha j) le_rfl (hε _)
    (hout.2 (X (j - 1)).Y0 (X (j - 1)).U (X (j - 1)).Uw (X (j - 1)).Uk (htr j hj hjn) hsol')

/-- Lift coefficients for every level, from the certificates of the passages. -/
theorem cascade_lifts_exist (N depth sX sZ n m₀ : ℕ) (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (h : ∀ j, m₀ < j → j ≤ n → ∃ CcT : ℤ → ℕ → ℕ →
      LiftCoeff (CompIn (stage j).comps) (fun v => ScalarH v.1.root),
      IsPassageLift (stage j) j N depth sX sZ CcT) :
    ∃ CcT : (j : ℕ) → ℤ → ℕ → ℕ →
        LiftCoeff (CompIn (stage j).comps) (fun v => ScalarH v.1.root),
      ∀ j, m₀ < j → j ≤ n → IsPassageLift (stage j) j N depth sX sZ (CcT j) := by
  classical
  have h' : ∀ j, ∃ CcT : ℤ → ℕ → ℕ →
      LiftCoeff (CompIn (stage j).comps) (fun v => ScalarH v.1.root),
      m₀ < j → j ≤ n → IsPassageLift (stage j) j N depth sX sZ CcT := by
    intro j
    by_cases hj : m₀ < j ∧ j ≤ n
    · obtain ⟨CcT, hCcT⟩ := h j hj.1 hj.2
      exact ⟨CcT, fun _ _ => hCcT⟩
    · exact ⟨fun _ _ _ _ _ _ _ _ _ _ => 0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose CcT hCcT using h'
  exact ⟨CcT, hCcT⟩

/-- Classical representatives for every level on the nested windows of the passages. -/
theorem cascade_reps_exist (k n m₀ : ℕ) (hm : m₀ < n) (tS t₀ tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (st tp : ℕ → ℝ)
    (U : (j : ℕ) → ∀ v : CompIn (stage j).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (hst : ∀ j, m₀ < j → j ≤ n → st (j - 1) = tp j)
    (hsp : ∀ j, m₀ < j → j ≤ n → st j ≤ tp j)
    (htp : ∀ j, m₀ < j → j ≤ n → tp j ≤ tS + t₀)
    (hcl : ∀ j, m₀ < j → j ≤ n →
      ∃ (aU : ℝ → Vec 2 → ∀ v : CompIn (stage j).comps, ScalarH v.1.root)
        (aY : ℝ → Vec 2 → ∀ v : CompIn (stage (j - 1)).comps, ScalarH v.1.root),
        (∀ t ∈ Set.Icc (tp j) tf, IsSmoothRep (fun v => U j v t) (aU t) k) ∧
        (∀ t ∈ Set.Icc (tp j) tf, IsSmoothRep (fun v => U (j - 1) v t) (aY t) k)) :
    ∃ aU : (j : ℕ) → ℝ → Vec 2 → ∀ v : CompIn (stage j).comps, ScalarH v.1.root,
      (∀ j, m₀ < j → j ≤ n → ∀ t ∈ Set.Icc (tp j) tf,
        IsSmoothRep (fun v => U j v t) (aU j t) k ∧
        IsSmoothRep (fun v => U (j - 1) v t) (aU (j - 1) t) k) ∧
      (∀ t ∈ Set.Icc (tS + t₀) tf, IsSmoothRep (fun v => U n v t) (aU n t) k) ∧
      ∀ t ∈ Set.Icc (tS + t₀) tf, IsSmoothRep (fun v => U m₀ v t) (aU m₀ t) k := by
  classical
  -- the window of the level `j`: `[t_p^{(n)}, t_f]` for `j = n`, `[s_j, t_f]` below
  obtain ⟨w, hwn, hwj⟩ : ∃ w : ℕ → ℝ, w n = tp n ∧ ∀ j, j ≠ n → w j = st j :=
    ⟨fun j => if j = n then tp n else st j, by simp only [↓reduceIte],
      fun j hj => by simp only [hj, ↓reduceIte]⟩
  have h' : ∀ j, ∃ a : ℝ → Vec 2 → ∀ v : CompIn (stage j).comps, ScalarH v.1.root,
      m₀ ≤ j → j ≤ n → ∀ t ∈ Set.Icc (w j) tf, IsSmoothRep (fun v => U j v t) (a t) k := by
    intro j
    by_cases hj : m₀ ≤ j ∧ j ≤ n
    · by_cases hjn : j = n
      · subst hjn
        obtain ⟨aU, -, haU, -⟩ := hcl j hm le_rfl
        refine ⟨aU, fun _ _ t ht => haU t ?_⟩
        rw [hwn] at ht
        exact ht
      · have hlt : j < n := lt_of_le_of_ne hj.2 hjn
        obtain ⟨-, aY, -, haY⟩ := hcl (j + 1) (by omega) (by omega)
        refine ⟨aY, fun _ _ t ht => haY t ?_⟩
        have hs : st j = tp (j + 1) := hst (j + 1) (by omega) (by omega)
        rw [hwj j hjn, hs] at ht
        exact ht
    · exact ⟨fun _ _ _ => 0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose aU haU using h'
  refine ⟨aU, fun j hj hjn t ht => ⟨?_, ?_⟩, fun t ht => ?_, fun t ht => ?_⟩
  · refine haU j hj.le hjn t ?_
    by_cases hjn' : j = n
    · subst hjn'
      rw [hwn]
      exact ht
    · rw [hwj j hjn']
      exact ⟨(hsp j hj hjn).trans ht.1, ht.2⟩
  · refine haU (j - 1) (by omega) (by omega) t ?_
    rw [hwj (j - 1) (by omega), hst j hj hjn]
    exact ht
  · refine haU n hm.le le_rfl t ?_
    rw [hwn]
    exact ⟨(htp n hm le_rfl).trans ht.1, ht.2⟩
  · refine haU m₀ le_rfl hm.le t ?_
    have hs : st m₀ = tp (m₀ + 1) := hst (m₀ + 1) (by omega) (by omega)
    rw [hwj m₀ (by omega), hs]
    exact ⟨(htp (m₀ + 1) (by omega) (by omega)).trans ht.1, ht.2⟩
end

end AVRegularity.IterationPassage.Cascade
end
end
end
