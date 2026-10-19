-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.IterationPassage.Cascade.RunAssembly
import AVRegularity.Proofs.Results.Iteration.PassageErrorJets
import AVRegularity.IterationPassage.Cascade.Recursion
import AVRegularity.IterationPassage.Passage.OfProfiles
import AVRegularity.IterationPassage.Passage.Profiles.RetainedCov
import AVRegularity.IterationPassage.Passage.Profiles.DiscardedDeClose
public import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
public import AVRegularity.IterationPassage.Passage.Profiles.ClausesStatement

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.IterationPassage.Cascade

/-! **The data of a datum along a run, bundled**.

The proof of `CascadeOutput` for one datum is split along two bundles, each a structure in
`Prop`, so that every step has a short statement:

* `RunDatum … f X a`: families `X j` of the datum `f` (solutions from `s_j`, retained traces),
  marked amplitudes `≤ a j` on `[s_j, t_f]`, and `PassageDatum` of every passage at the
  intermediate constant `C₁` and the amplitude `a j`.
* `RunReps … X aU CcT rep`: lift coefficients, classical representatives on the windows of the
  passages and on `I_* = [t_S + t₀, t_f]`, and the two defining clauses of `rep`.

Steps: `runDatum_exists` (families, amplitudes from `AmplitudeAt`, certificates),
`runReps_exist` (choice and upward recursion), `run_bottom` (the bottom bound on `I_*` from
`BottomAt` and the regenerated solution of the passage `m₀ + 1`), `run_size` (the size of `rep n`
on `I_*`, `cascade_size_of_parts`).

The degenerate cases are included: `n = m₀ + 1`; `f = 0`; an empty family. -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The families of a datum `f` along a run, with amplitudes `a j` and the certificate of every
passage at the constant `C₁`. -/
structure RunDatum (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q C₁ cr c₀ : ℝ) (n m₀ : ℕ) (tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ) {Nout : ℕ}
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root))
    (X : (j : ℕ) → StageFam (stage j)) (a : ℕ → ℝ) : Prop where
  /-- The top datum. -/
  top : (X n).Y0 = f
  /-- The solutions. -/
  sol : ∀ j, m₀ ≤ j → j ≤ n →
    StageSol P seedK freshK φ₀ hφ₀ (stage j) j (st j) tf (X j).Y0 (X j).U (X j).Uw (X j).Uk
  /-- The retained traces. -/
  tr : ∀ j, m₀ < j → j ≤ n →
    IsRetainedTrace (stage j) (stage (j - 1)) j p (tp j)
      (Preg j (fun v => (X j).U v (cascadeRestart D hist st j))) (X (j - 1)).Y0
  /-- The marked amplitudes. -/
  amp : ∀ j, m₀ ≤ j → j ≤ n → ∀ t ∈ Set.Icc (st j) tf,
    weightedNorm 1 ((stage j).mass law) ((stage j).marker law) (fun v => (X j).U v t) ≤ a j
  /-- The certificates of the passages. -/
  datum : ∀ j, m₀ < j → j ≤ n →
    PassageDatum law P seedK freshK φ₀ hφ₀ (stage j) (stage (j - 1)) j p N depth sX sZ K Naux
      s η₀ mu wexp Pacc Q C₁ cr c₀ (a j) (cascadeRestart D hist st j) (tp j) tf (freshK (j - 1))
      (Preg j) (fun v => (X j).U v (cascadeRestart D hist st j)) (X j).U (X (j - 1)).U

/-- Lift coefficients, classical representatives and the representation along a run. -/
structure RunReps (law : BirthLaw) (freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (p N depth sX sZ K : ℕ) (η₀ : ℝ) (n m₀ : ℕ) (tS t₀ tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (tp : ℕ → ℝ)
    (X : (j : ℕ) → StageFam (stage j))
    (aU : (j : ℕ) → ℝ → Vec 2 → ∀ v : CompIn (stage j).comps, ScalarH v.1.root)
    (CcT : (j : ℕ) → ℤ → ℕ → ℕ →
      LiftCoeff (CompIn (stage j).comps) (fun v => ScalarH v.1.root))
    (rep : (j : ℕ) → TimeRep (CompSpace (stage j).comps)) : Prop where
  /-- The lifts. -/
  lift : ∀ j, m₀ < j → j ≤ n → IsPassageLift (stage j) j N depth sX sZ (CcT j)
  /-- The representatives on the windows of the passages. -/
  reps : ∀ j, m₀ < j → j ≤ n → ∀ t ∈ Set.Icc (tp j) tf,
    IsSmoothRep (fun v => (X j).U v t) (aU j t) (K + N + 2 * p + 2) ∧
    IsSmoothRep (fun v => (X (j - 1)).U v t) (aU (j - 1) t) (K + N + 2 * p + 2)
  /-- The representative of the top solution on `I_*`. -/
  repn : ∀ t ∈ Set.Icc (tS + t₀) tf,
    IsSmoothRep (fun v => (X n).U v t) (aU n t) (K + N + 2 * p + 2)
  /-- The representative of the bottom solution on `I_*`. -/
  repm : ∀ t ∈ Set.Icc (tS + t₀) tf,
    IsSmoothRep (fun v => (X m₀).U v t) (aU m₀ t) (K + N + 2 * p + 2)
  /-- The recursion of the representation. -/
  recur : ∀ j, m₀ < j → j ≤ n →
    rep j = ((rep (j - 1)).map (readoutCLM j (D.eps (j - 1)) η₀ ((stage j).mass law)
        ((stage (j - 1)).mass law))).append
      (passageProfiles D law (stage j) (stage (j - 1)) j p N depth η₀ φ₀ (freshK (j - 1))
        (CcT j) (aU j) (aU (j - 1)))
  /-- The base of the representation. -/
  base : rep m₀ = ⟨fun t => compField ((stage m₀).mass law) (aU m₀ t), []⟩

/-- **The families of a datum with their amplitudes and certificates.** -/
theorem runDatum_exists (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q Cpass Ca C₁ cr c₀ : ℝ) (n m₀ : ℕ) (hm : m₀ ≤ n) (tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ) {Nout : ℕ}
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root)))
    (hC : Cpass ≤ C₁) (hC₁ : 0 ≤ C₁) (hCa : 0 ≤ Ca) (hε : ∀ k, 0 ≤ D.eps k)
    (hst : ∀ j, m₀ < j → j ≤ n → st (j - 1) = tp j)
    (hr : ∀ j, m₀ < j → j ≤ n → cascadeRestart D hist st j ≤ tf)
    (hpass : ∀ j, m₀ < j → j ≤ n →
      PassageOutput law P seedK freshK φ₀ hφ₀ (stage j) (stage (j - 1)) j p N depth sX sZ K Naux
        s η₀ mu wexp Pacc Q Cpass cr c₀ (cascadeRestart D hist st j) (tp j) tf (freshK (j - 1))
        (Preg j))
    (hamp : AmplitudeAt law P seedK freshK φ₀ hφ₀ p Q Ca n m₀ tf stage hist st tp Preg)
    (top : StageFam (stage n))
    (htop : StageSol P seedK freshK φ₀ hφ₀ (stage n) n (st n) tf top.Y0 top.U top.Uw top.Uk) :
    ∃ X : (j : ℕ) → StageFam (stage j),
      RunDatum law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C₁ cr c₀ n m₀ tf stage hist st tp Preg top.Y0 X
        (fun j => ampRef D Ca Q n (weightedNorm 1 ((stage n).mass law) (fun _ => 1) top.Y0) j) ∧
      ∀ j, m₀ ≤ j → j ≤ n →
        ampRef D Ca Q n (weightedNorm 1 ((stage n).mass law) (fun _ => 1) top.Y0) j ≤
          Ca * weightedNorm 1 ((stage n).mass law) (fun _ => 1) top.Y0 := by
  obtain ⟨X, hXn, hsol, htr⟩ := cascade_families_exist law P seedK freshK φ₀ hφ₀ p N depth sX sZ
    K Naux s η₀ mu wexp Pacc Q Cpass cr c₀ n m₀ hm tf stage hist st tp Preg hst hpass top htop
  have hY0 : (X n).Y0 = top.Y0 := by rw [hXn]
  have hA := hamp top.Y0 (fun j => (X j).U) (fun j => (X j).Uw) (fun j => (X j).Uk)
    (fun j => (X j).Y0) hY0 hsol htr
  have hnf0 : 0 ≤ weightedNorm 1 ((stage n).mass law) (fun _ => 1) top.Y0 := Real.sqrt_nonneg _
  refine ⟨X, ⟨hY0, hsol, htr, fun j hj hjn => (hA j hj hjn).1, ?_⟩,
    fun j hj hjn => (hA j hj hjn).2⟩
  exact cascade_passage_datum law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀ mu wexp
    Pacc Q Cpass C₁ cr c₀ n m₀ tf stage hist st tp Preg X _ hC hC₁
    (fun j => ampRef_nonneg D Ca Q n _ j hCa hnf0 hε) hε hst hr hpass hsol htr
    (fun j hj hjn => (hA j hj hjn).1)

/-- **Lifts, representatives and the representation of a datum along a run.** -/
theorem runReps_exist (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q C₁ cr c₀ : ℝ) (n m₀ : ℕ) (hm : m₀ < n) (tS t₀ tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ) {Nout : ℕ}
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root))
    (X : (j : ℕ) → StageFam (stage j)) (a : ℕ → ℝ)
    (hst : ∀ j, m₀ < j → j ≤ n → st (j - 1) = tp j)
    (hsp : ∀ j, m₀ < j → j ≤ n → st j ≤ tp j)
    (htp : ∀ j, m₀ < j → j ≤ n → tp j ≤ tS + t₀)
    (h : RunDatum law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C₁ cr c₀ n m₀ tf stage hist st tp Preg f X a) :
    ∃ (aU : (j : ℕ) → ℝ → Vec 2 → ∀ v : CompIn (stage j).comps, ScalarH v.1.root)
      (CcT : (j : ℕ) → ℤ → ℕ → ℕ →
      LiftCoeff (CompIn (stage j).comps) (fun v => ScalarH v.1.root))
      (rep : (j : ℕ) → TimeRep (CompSpace (stage j).comps)),
      RunReps law freshK φ₀ p N depth sX sZ K η₀ n m₀ tS t₀ tf stage tp X aU CcT rep := by
  obtain ⟨CcT, hCcT⟩ := cascade_lifts_exist N depth sX sZ n m₀ stage (fun j hj hjn =>
    passageDatum_exists_lift law P seedK freshK φ₀ hφ₀ (stage j) (stage (j - 1)) j p N depth sX sZ
      K Naux s η₀ mu wexp Pacc Q C₁ cr c₀ _ _ (tp j) tf (freshK (j - 1)) (Preg j) _ _ _
      (h.datum j hj hjn))
  obtain ⟨aU, hreps, hrepn, hrepm⟩ := cascade_reps_exist (K + N + 2 * p + 2) n m₀ hm tS t₀ tf
    stage st tp (fun j => (X j).U) hst hsp htp (fun j hj hjn => (h.datum j hj hjn).2.2.1.1)
  obtain ⟨rep, hrep0, hrepS⟩ := exists_upward_family
    (T := fun j => TimeRep (CompSpace (stage j).comps)) m₀
    (fun j => ⟨fun t => compField ((stage j).mass law) (aU j t), []⟩)
    (fun k r => (r.map (readoutCLM (k + 1) (D.eps k) η₀ ((stage (k + 1)).mass law)
        ((stage k).mass law))).append
      (passageProfiles D law (stage (k + 1)) (stage k) (k + 1) p N depth η₀ φ₀ (freshK k)
        (CcT (k + 1)) (aU (k + 1)) (aU k)))
  refine ⟨aU, CcT, rep, hCcT, hreps, hrepn, hrepm, fun j hj hjn => ?_, hrep0⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact hrepS k (by omega)

/-- **The bottom bound on `I_*`** from the regenerated solution of the passage `m₀ + 1`. -/
theorem run_bottom (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q C₁ cr c₀ Cb Z : ℝ) (n m₀ : ℕ) (hm : m₀ < n) (tS t₀ tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ) {Nout : ℕ}
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root))
    (X : (j : ℕ) → StageFam (stage j)) (a : ℕ → ℝ)
    (aU : (j : ℕ) → ℝ → Vec 2 → ∀ v : CompIn (stage j).comps, ScalarH v.1.root)
    (CcT : (j : ℕ) → ℤ → ℕ → ℕ →
      LiftCoeff (CompIn (stage j).comps) (fun v => ScalarH v.1.root))
    (rep : (j : ℕ) → TimeRep (CompSpace (stage j).comps))
    (htp : tp (m₀ + 1) ≤ tS + t₀)
    (h : RunDatum law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C₁ cr c₀ n m₀ tf stage hist st tp Preg f X a)
    (hR : RunReps law freshK φ₀ p N depth sX sZ K η₀ n m₀ tS t₀ tf stage tp X aU CcT rep)
    (hbot : BottomAt law (stage m₀) (m₀ + 1) K Naux s cr Cb (D.eps m₀) Z) :
    ∀ t ∈ Set.Icc (tS + t₀) tf, representedSize s K (D.eps m₀)
      (⟨compField ((stage m₀).mass law) (aU m₀ t), []⟩ :
        Representation (CompSpace (stage m₀).comps)) ≤
      ENNReal.ofReal (Cb * D.eps m₀ ^ (-Z) * (C₁ * a (m₀ + 1))) := by
  intro t ht
  obtain ⟨-, ⟨YN0, YN, YNw, YNk, -, -, htrunc, hpt, -, -⟩, -, -⟩ :=
    h.datum (m₀ + 1) (by omega) (by omega)
  have htW : t ∈ Set.Icc (tp (m₀ + 1)) tf := ⟨htp.trans ht.1, ht.2⟩
  have hrep := hR.repm t ht
  refine hbot (fun v => YN v t) (aU m₀ t) _
    (hrep.1.of_le (by exact_mod_cast (by omega : K ≤ K + N + 2 * p + 2))) hrep.2.1
    (fun v => ?_) (hpt t htW)
  have h1 := IterationPassage.torus_truncate_value_ae (Nat.zero_le Naux) (YN v t)
  rw [htrunc v t htW] at h1
  exact h1.symm.trans (hrep.2.2 v)

/-- **The size of `rep n` on `I_*`.** -/
theorem run_size (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q C₁ cr c₀ : ℝ) (n m₀ : ℕ) (hm : m₀ < n) (tS t₀ tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ) {Nout : ℕ}
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root))
    (X : (j : ℕ) → StageFam (stage j)) (a : ℕ → ℝ)
    (aU : (j : ℕ) → ℝ → Vec 2 → ∀ v : CompIn (stage j).comps, ScalarH v.1.root)
    (CcT : (j : ℕ) → ℤ → ℕ → ℕ →
      LiftCoeff (CompIn (stage j).comps) (fun v => ScalarH v.1.root))
    (rep : (j : ℕ) → TimeRep (CompSpace (stage j).comps))
    (htp : ∀ j, m₀ < j → j ≤ n → tp j ≤ tS + t₀) (hε : ∀ k, 0 < D.eps k ∧ D.eps k ≤ 1)
    (hC₁ : 0 ≤ C₁) (ha : ∀ j, 0 ≤ a j)
    (h : RunDatum law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C₁ cr c₀ n m₀ tf stage hist st tp Preg f X a)
    (hR : RunReps law freshK φ₀ p N depth sX sZ K η₀ n m₀ tS t₀ tf stage tp X aU CcT rep)
    (Xb Tg Tc : ℝ) (hXb : 0 ≤ Xb)
    (hbot : ∀ t ∈ Set.Icc (tS + t₀) tf, representedSize s K (D.eps m₀)
      (⟨compField ((stage m₀).mass law) (aU m₀ t), []⟩ :
        Representation (CompSpace (stage m₀).comps)) ≤ ENNReal.ofReal Xb)
    (hTg : ∑ j ∈ Finset.Ioc m₀ n, C₁ * (D.eps (j - 1) ^ (5 * η₀ / 4) + D.eps (j - 1) ^ mu +
      D.eps (j - 1) ^ wexp) ≤ Tg)
    (hTc : ∑ j ∈ Finset.Ioc m₀ n, C₁ * D.eps (j - 1) ^ Pacc * a j ≤ Tc) :
    ∀ t ∈ Set.Icc (tS + t₀) tf,
      IsRepresentationAt (D.eps n) K ((rep n).atTime t) ∧
      ((rep n).atTime t).value = compField ((stage n).mass law) (aU n t) ∧
      representedSize s K (D.eps n) ((rep n).atTime t) ≤
        ENNReal.ofReal (Real.exp Tg * (Xb + Tc)) :=
  cascade_size_of_parts law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C₁
    cr c₀ n m₀ tS t₀ tf stage hist st tp Preg (fun j => (X j).U) aU CcT rep a hm htp hε hC₁ ha
    h.datum hR.lift hR.reps hR.recur hR.base Xb Tg Tc hXb hbot hTg hTc
end

/-! **`CascadeOutput` for one datum from the parts**.

`cascadeOutput_of_parts`: for a frame of the cascade whose passages have their `PassageOutput` at
the constant `C_pass`, and a datum `f` on the top stage: `CascadeOutput` with the constant `C`,
from

* the order-zero solution of the top stage from `f` (`htop`);
* the amplitude theorem at the data (`AmplitudeAt`, constant `C_a > 0`);
* the bottom bound at the passage `m₀ + 1` (`BottomAt`, constant `C_b ≥ 0`, exponent `Z`);
* bounds `T`, `T_P` of the sums of the three recurrence exponents and of `ε^P` over `(m₀, n]`;
* an intermediate constant `C₁ ≥ max{C_pass, C_a, 1}`, and
  `C ≥ C₁`, `C ≥ exp(C₁T)(C_b ε_{m₀}^{-Z} C₁C_a + C₁C_aT_P)`.

Steps: families downward (`cascade_families_exist`); amplitudes
`a_j = ampRef D C_a Q n ‖f‖ j`; the certificate of every passage at `(C₁, a_j)`
(`cascade_passage_datum`); lifts and representatives by choice; `rep` by upward recursion; the
size on `I_*` (`cascade_size_of_parts`) with the bottom bound; the final lift to
`(C, ampRef D C Q n ‖f‖ j)` by `passageDatum_mono` and `ampRef_mono`. All
estimates run at `C₁` and `a_j`, which do not depend on the bottom level; `C` enters at the end.

The proof is split along the bundles `RunDatum`, `RunReps`, so that every step has a short
statement. `cascadeOutput_of_run` is the packaging and the final
lift; `cascade_final_bound`, `cascade_sum_bound` are the two real inequalities.

The degenerate cases are included: `n = m₀ + 1` (one passage, the bottom is its outgoing solution);
`f = 0` (`a_j = 0`, all bounds `0 ≤ 0`); an empty family. -/

section
/-- The sum `∑ C₁ E_j a_j` over `(m₀, n]` when `a_j ≤ B` there. -/
theorem cascade_sum_bound (E a : ℕ → ℝ) (m₀ n : ℕ) {C₁ B TP : ℝ} (hC₁ : 0 ≤ C₁) (hB : 0 ≤ B)
    (hE : ∀ j, 0 ≤ E j) (hab : ∀ j, m₀ < j → j ≤ n → a j ≤ B)
    (hsum : ∑ j ∈ Finset.Ioc m₀ n, E j ≤ TP) :
    ∑ j ∈ Finset.Ioc m₀ n, C₁ * E j * a j ≤ C₁ * B * TP := by
  calc ∑ j ∈ Finset.Ioc m₀ n, C₁ * E j * a j
      ≤ ∑ j ∈ Finset.Ioc m₀ n, C₁ * B * E j := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' := Finset.mem_Ioc.mp hj
        have h := mul_le_mul_of_nonneg_left (hab j hj'.1 hj'.2) (mul_nonneg hC₁ (hE j))
        linarith
    _ = C₁ * B * ∑ j ∈ Finset.Ioc m₀ n, E j := by rw [Finset.mul_sum]
    _ ≤ C₁ * B * TP := mul_le_mul_of_nonneg_left hsum (mul_nonneg hC₁ hB)

/-- The final inequality of the cascade: the size bound at the intermediate constant is at most
`C‖f‖`. -/
theorem cascade_final_bound {C₁ T Cb w Ca TP C nf am : ℝ} (hCb : 0 ≤ Cb) (hw : 0 ≤ w)
    (hC₁ : 0 ≤ C₁) (hnf : 0 ≤ nf) (hb : am ≤ Ca * nf)
    (hCsize : Real.exp (C₁ * T) * (Cb * w * (C₁ * Ca) + C₁ * Ca * TP) ≤ C) :
    Real.exp (C₁ * T) * (Cb * w * (C₁ * am) + C₁ * (Ca * nf) * TP) ≤ C * nf := by
  have h1 : Cb * w * (C₁ * am) ≤ Cb * w * (C₁ * (Ca * nf)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hC₁) (mul_nonneg hCb hw)
  have h2 := mul_le_mul_of_nonneg_left (add_le_add h1 (le_refl (C₁ * (Ca * nf) * TP)))
    (Real.exp_pos (C₁ * T)).le
  have h3 := mul_le_mul_of_nonneg_right hCsize hnf
  have he : Real.exp (C₁ * T) * (Cb * w * (C₁ * (Ca * nf)) + C₁ * (Ca * nf) * TP) =
      Real.exp (C₁ * T) * (Cb * w * (C₁ * Ca) + C₁ * Ca * TP) * nf := by ring
  linarith

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **`CascadeOutput` from the bundles of a run**: packaging and the final lift of the constant
and of the amplitudes. -/
theorem cascadeOutput_of_run (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q C₁ C cr c₀ : ℝ) (n m₀ : ℕ) (tS t₀ tf : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ) {Nout : ℕ}
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root)))
    (f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root))
    (X : (j : ℕ) → StageFam (stage j)) (a : ℕ → ℝ)
    (aU : (j : ℕ) → ℝ → Vec 2 → ∀ v : CompIn (stage j).comps, ScalarH v.1.root)
    (CcT : (j : ℕ) → ℤ → ℕ → ℕ →
      LiftCoeff (CompIn (stage j).comps) (fun v => ScalarH v.1.root))
    (rep : (j : ℕ) → TimeRep (CompSpace (stage j).comps))
    (hC₁C : C₁ ≤ C) (hC0 : 0 ≤ C) (ha0 : ∀ j, 0 ≤ a j) (hε : ∀ k, 0 ≤ D.eps k)
    (haC : ∀ j, a j ≤ ampRef D C Q n (weightedNorm 1 ((stage n).mass law) (fun _ => 1) f) j)
    (h : RunDatum law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C₁ cr c₀ n m₀ tf stage hist st tp Preg f X a)
    (hR : RunReps law freshK φ₀ p N depth sX sZ K η₀ n m₀ tS t₀ tf stage tp X aU CcT rep)
    (hsize : ∀ t ∈ Set.Icc (tS + t₀) tf,
      IsRepresentationAt (D.eps n) K ((rep n).atTime t) ∧
      ((rep n).atTime t).value = compField ((stage n).mass law) (aU n t) ∧
      representedSize s K (D.eps n) ((rep n).atTime t) ≤ ENNReal.ofReal (C * (weightedNorm 1 ((stage n).mass law) (fun _ => 1) f))) :
    CascadeOutput law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C cr c₀ n
      m₀ tS t₀ tf stage hist st tp Preg f :=
  ⟨fun j => (X j).U, fun j => (X j).Uw, fun j => (X j).Uk, fun j => (X j).Y0, aU, CcT, rep, h.top,
    fun j hj hjn => ⟨h.sol j hj hjn, stageSol_restart P seedK freshK φ₀ hφ₀ (stage j) j (st j)
      (cascadeRestart D hist st j) tf (le_max_left _ _) _ _ _ _ (h.sol j hj hjn),
      fun t ht => (h.amp j hj hjn t ht).trans (haC j)⟩,
    fun j hj hjn => ⟨h.tr j hj hjn, passageDatum_mono law P seedK freshK φ₀ hφ₀ (stage j)
      (stage (j - 1)) j p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C₁ C cr c₀ _ _ _ (tp j) tf
      (freshK (j - 1)) (Preg j) _ _ _ hC₁C hC0 (ha0 j) (haC j) (hε _) (h.datum j hj hjn),
      hR.lift j hj hjn, hR.reps j hj hjn, hR.recur j hj hjn⟩,
    hR.repn, hR.base, fun t ht => ⟨(hsize t ht).1, (hsize t ht).2.1⟩,
    ae_restrict_of_forall_mem measurableSet_Icc fun t ht => (hsize t ht).2.2⟩

/-- **`CascadeOutput` for one datum from the parts.** -/
theorem cascadeOutput_of_parts (law : BirthLaw) (P : ProvParams) (Mn : SuccMenu)
    (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (Mnat : ℕ)
    (kI : InvConsts) (CI τe : ℝ) (Kres Tw p N depth sX sZ K Naux : ℕ)
    (s η₀ mu wexp Pacc Q CQ Cp Cpass Ca Cb Z T TP C₁ C cr c₀ : ℝ)
    (seed : GenStage D ScalarH Dm b j₀) (n m₀ : ℕ) (tS t₀ tf : ℝ)
    (stage ext : ℕ → GenStage D ScalarH Dm b j₀) (hist st tp : ℕ → ℝ) {Nout : ℕ}
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root)))
    (hΛ : 1 ≤ D.Λ) (hm : m₀ < n) (hε : ∀ k, 0 < D.eps k ∧ D.eps k ≤ 1) (hCa : 0 < Ca)
    (hCb : 0 ≤ Cb) (hC₁p : Cpass ≤ C₁) (hC₁a : Ca ≤ C₁) (hC₁1 : 1 ≤ C₁) (hC₁C : C₁ ≤ C)
    (hCsize : Real.exp (C₁ * T) * (Cb * D.eps m₀ ^ (-Z) * (C₁ * Ca) + C₁ * Ca * TP) ≤ C)
    (hsumg : ∑ j ∈ Finset.Ioc m₀ n, (D.eps (j - 1) ^ (5 * η₀ / 4) + D.eps (j - 1) ^ mu +
      D.eps (j - 1) ^ wexp) ≤ T)
    (hsumP : ∑ j ∈ Finset.Ioc m₀ n, D.eps (j - 1) ^ Pacc ≤ TP)
    (hframe : CascadeFrame law P Mn seedK freshK φ₀ hφ₀ Mnat kI CI τe η₀ Kres Tw p Nout Naux Q CQ
      Cp seed n m₀ tS t₀ tf stage ext hist st tp Preg)
    (hpass : ∀ j, m₀ < j → j ≤ n →
      PassageOutput law P seedK freshK φ₀ hφ₀ (stage j) (stage (j - 1)) j p N depth sX sZ K Naux
        s η₀ mu wexp Pacc Q Cpass cr c₀ (cascadeRestart D hist st j) (tp j) tf (freshK (j - 1))
        (Preg j))
    (htop : ∀ f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root),
      ∃ (U : ∀ v : CompIn (stage n).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
        (Uw : ∀ v : CompIn (stage n).comps, ℝ → TorusHk 1 (ScalarH v.1.root))
        (Uk : ∀ v u (_ : (stage n).fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
        StageSol P seedK freshK φ₀ hφ₀ (stage n) n (st n) tf f U Uw Uk)
    (hamp : AmplitudeAt law P seedK freshK φ₀ hφ₀ p Q Ca n m₀ tf stage hist st tp Preg)
    (hbot : BottomAt law (stage m₀) (m₀ + 1) K Naux s cr Cb (D.eps m₀) Z)
    (f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root)) :
    CascadeOutput law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C cr c₀ n
      m₀ tS t₀ tf stage hist st tp Preg f := by
  have hnf0 : 0 ≤ weightedNorm 1 ((stage n).mass law) (fun _ => 1) f := Real.sqrt_nonneg _
  have hεle : ∀ k, 0 ≤ D.eps k := fun k => (hε k).1.le
  have hC₁0 : 0 ≤ C₁ := zero_le_one.trans hC₁1
  have hC0 : 0 ≤ C := hC₁0.trans hC₁C
  have hCaC : Ca ≤ C := hC₁a.trans hC₁C
  obtain ⟨U₀, Uw₀, Uk₀, htop'⟩ := htop f
  obtain ⟨ht1, -⟩ := cascadeFrame_timing law P Mn seedK freshK φ₀ hφ₀ Mnat kI CI τe η₀ Kres Tw p
    Nout Naux Q CQ Cp seed n m₀ tS t₀ tf stage ext hist st tp Preg hΛ hframe
  have hst : ∀ j, m₀ < j → j ≤ n → st (j - 1) = tp j := fun j hj hjn =>
    (hframe.2.2.2.2.2 j hj hjn).2.2.2.1
  obtain ⟨X, hRD, hAb⟩ := runDatum_exists law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀
    mu wexp Pacc Q Cpass Ca C₁ cr c₀ n m₀ hm.le tf stage hist st tp Preg hC₁p hC₁0 hCa.le hεle hst
    (fun j hj hjn => (ht1 j hj hjn).2.2.1) hpass hamp ⟨f, U₀, Uw₀, Uk₀⟩ htop'
  obtain ⟨aU, CcT, rep, hR⟩ := runReps_exist law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s
    η₀ mu wexp Pacc Q C₁ cr c₀ n m₀ hm tS t₀ tf stage hist st tp Preg f X _ hst
    (fun j hj hjn => (ht1 j hj hjn).1.trans (ht1 j hj hjn).2.1)
    (fun j hj hjn => (ht1 j hj hjn).2.2.2) hRD
  have ha0 : ∀ j, 0 ≤ ampRef D Ca Q n (weightedNorm 1 ((stage n).mass law) (fun _ => 1) f) j := fun j =>
    ampRef_nonneg D Ca Q n _ j hCa.le hnf0 hεle
  have hw : 0 ≤ D.eps m₀ ^ (-Z) := Real.rpow_nonneg (hεle m₀) _
  have hbot' := run_bottom law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C₁
    cr c₀ Cb Z n m₀ hm tS t₀ tf stage hist st tp Preg f X _ aU CcT rep
    ((ht1 (m₀ + 1) (by omega) (by omega)).2.2.2) hRD hR hbot
  have hTg : ∑ j ∈ Finset.Ioc m₀ n, C₁ * (D.eps (j - 1) ^ (5 * η₀ / 4) + D.eps (j - 1) ^ mu +
      D.eps (j - 1) ^ wexp) ≤ C₁ * T := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsumg hC₁0
  have hTc := cascade_sum_bound (fun j => D.eps (j - 1) ^ Pacc)
    (fun j => ampRef D Ca Q n (weightedNorm 1 ((stage n).mass law) (fun _ => 1) f) j) m₀ n hC₁0 (mul_nonneg hCa.le hnf0)
    (fun j => Real.rpow_nonneg (hεle (j - 1)) Pacc) (fun j hj hjn => hAb j hj.le hjn) hsumP
  have hsize := run_size law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀ mu wexp Pacc Q C₁
    cr c₀ n m₀ hm tS t₀ tf stage hist st tp Preg f X _ aU CcT rep
    (fun j hj hjn => (ht1 j hj hjn).2.2.2) hε hC₁0 ha0 hRD hR _ _ _
    (mul_nonneg (mul_nonneg hCb hw) (mul_nonneg hC₁0 (ha0 _))) hbot' hTg hTc
  have hfinal := cascade_final_bound hCb hw hC₁0 hnf0 (hAb (m₀ + 1) (by omega) (by omega)) hCsize
  exact cascadeOutput_of_run law P seedK freshK φ₀ hφ₀ p N depth sX sZ K Naux s η₀ mu wexp Pacc Q
    C₁ C cr c₀ n m₀ tS t₀ tf stage hist st tp Preg f X _ aU CcT rep hC₁C hC0 ha0 hεle
    (fun j => ampRef_mono D Ca C Q n _ j hCa.le hCaC hnf0 hεle) hRD hR
    (fun t ht => ⟨(hsize t ht).1, (hsize t ht).2.1,
      ((hsize t ht).2.2).trans (ENNReal.ofReal_le_ofReal hfinal)⟩)
end

end AVRegularity.IterationPassage.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.Cascade

/-! **The amplitude theorem of the cascade with its data part named**.

`CascadeAmplitudeData` is the data part of `cascade_amplitude_product`
after its constants `C_Q, C_p`, `C, m_A` and the bottom
level `m₀ ≥ m_A`; `CascadeAmplitudeStatement` is the statement with that part named and
`cascadeAmplitude` is its proof (definitional unfolding). -/

/-- The data part of `cascade_amplitude_product`. -/
def CascadeAmplitudeData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw t₀ T₀ : ℝ) (r₀ D₀ : ℕ) (τe Q : ℝ) (H J N p nk Naux Nout Kres npad sX sZ : ℕ) (σ₀ Ce : ℝ)
    (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cp C : ℝ) (m₀ : ℕ) : Prop :=
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
      m₀ < n → n < M →
    ∀ (stage ext : ℕ → GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (hist st tp : ℕ → ℝ)
      (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn (stage j).comps, TorusHk Nout (ScalarH v.1.root))),
      CascadeFrame law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seedK freshK φ₀ hφ₀ Mnat kI CI τe
        (succEta0 α q s) Kres (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card p Nout
        Naux Q CQ Cp seed n m₀ tS t₀ tf stage ext hist st tp Preg →
    ∀ (f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root))
      (U : (j : ℕ) → ∀ v : CompIn (stage j).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Uw : (j : ℕ) → ∀ v : CompIn (stage j).comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Uk : (j : ℕ) → ∀ v u (_ : (stage j).fam.Γ v u), ℝ →
        TorusHk (0 + (succSchedD D₀ N p (H + 1)) - 1) (ScalarH u.1.root))
      (Y0 : (j : ℕ) → ∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)),
      Y0 n = f →
      (∀ j, m₀ ≤ j → j ≤ n →
        (stage j).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
          φ₀ hφ₀ (D.κ j) (streamVel (D.Φ j)) 0 (st j) tf (Y0 j) (fun _ _ => 0) (fun _ _ => 0)
          (U j) (Uw j) (Uk j)) →
      (∀ j, m₀ < j → j ≤ n →
        IsRetainedTrace (stage j) (stage (j - 1)) j p (tp j)
          (Preg j (fun v => U j v (cascadeRestart D hist st j))) (Y0 (j - 1))) →
    ∀ j, m₀ ≤ j → j ≤ n →
      (∀ t ∈ Set.Icc (st j) tf,
        weightedNorm 1 ((stage j).mass law) ((stage j).marker law) (fun v => U j v t) ≤
          ampRef D C Q n (weightedNorm 1 ((stage n).mass law) (fun _ => 1) f) j) ∧
      ampRef D C Q n (weightedNorm 1 ((stage n).mass law) (fun _ => 1) f) j ≤
        C * weightedNorm 1 ((stage n).mass law) (fun _ => 1) f

/-- `cascade_amplitude_product` with its data part named. -/
def CascadeAmplitudeStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc t₀ T₀ : ℝ), 3 ≤ K → 0 < Pacc → 0 < t₀ → t₀ < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (Q : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ) (σ₀ a σ : ℝ),
      IsCascadeSchedule α s q K Pacc lamE σE D₀ Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a σ →
    ∀ npad : ℕ, ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cp : ℝ, ∃ (C : ℝ) (mA : ℕ), 0 < C ∧ ∀ m₀ : ℕ, mA ≤ m₀ →
    CascadeAmplitudeData α s q ζ Λ φ₀ hφ₀ bw t₀ T₀ r₀ D₀ τe Q H J N p nk Naux Nout Kres npad sX sZ
      σ₀ Ce kS kI CI Cw j₀ CQ Cp C m₀

/-- The statement `cascade_amplitude_product`. -/
theorem cascadeAmplitude (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    CascadeAmplitudeStatement α s q ζ :=
  Providers.cascade_amplitude_product α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.IterationPassage.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.IterationPassage.Cascade

/-! **The families of the cascade from the bottom bound**.

`cascadeFamilies_of_bottom`: `CascadeFamiliesStatement` from the bottom bound
`CascadeBottomStatement`. The statement `cascade_amplitude_product` is applied
directly (`cascadeAmplitude`); it is the only input with the long prefix, so the families statement
takes its `Λ₀` (maximum with the one of the bottom bound), `c₀max` (minimum with `1`), lift floors,
thresholds, carrier constants and ledger thresholds unchanged, and `K_need := 0`.

Constants, in order, after `C_pass, C_Q, C_p`: `(C_a, m_a)` of the amplitude theorem;
`(C_b, m_B)` of the bottom bound at `(K, kI.c_r)`; the tails `T₁, T₂, T₃, T_P` of
`∑ ε_{k-1}^p` for `p = 5η₀/4, μ_s, δ - 2σ₀, P` (`scale_sum_tail`); the floor level `m_T` for
`C_I ε_j^{q·min(δ/4, τ_e)} ≤ 1/8` (`scale_floor`); `m_A := max{m_a, m_B, m_T + 1, j₀, 1}`; then
for `m₀ ≥ m_A`: `C₁ := max{C_pass, C_a, 1}` and
`C := max C₁ (exp(C₁(T₁+T₂+T₃))(C_b ε_{m₀}^{-Z_K} C₁C_a + C₁C_aT_P))`, the only place where the
constant depends on `m₀`.

At the data: the order-zero solution of the seed stage from `f` (`stageSol_exists`, with the
invariant of the frame at `j = n`), `AmplitudeAt` and `BottomAt` from the data statements, and
`cascadeOutput_of_parts`.

The degenerate cases are included: `n = m₀ + 1`; `f = 0`; an empty seed family. -/

/-- The data part of the families of the cascade from the data parts of the amplitude theorem and
of the bottom bound. -/
theorem cascadeFamiliesData_of_parts {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ}
    {hφ₀ : Integrable φ₀} {bw : ℝ} {K : ℕ} {Pacc t₀ T₀ : ℝ} {r₀ D₀ : ℕ} {τe Q : ℝ}
    {H J N p nk Naux Nout Kres npad sX sZ : ℕ} {σ₀ Ce : ℝ} {kS kI : InvConsts} {CI Cw : ℝ}
    {j₀ : ℕ} (hq : IsAdmissibleQ α s q) (hζf : IsFastProfile ζ) (hΛ : 128 ≤ Λ) (hbw : 0 < bw)
    (ht₀ : 0 < t₀) (hη : 0 < succEta0 α q s) (hc₀ : 0 < kI.c₀) (hc₀1 : kI.c₀ ≤ 1)
    (hHprod : kI.Hprod = kI.G0 + H + 1) (hNaux : K + 2 ≤ Naux)
    (Cpass CQ Cp Ca Cb T TP C₁ C : ℝ) (mB mT m₀ : ℕ) (hmB : mB ≤ m₀ + 1) (hmT : mT + 1 ≤ m₀)
    (hj₀ : j₀ ≤ m₀) (hm1 : 1 ≤ m₀) (hCa : 0 < Ca) (hCb : 0 ≤ Cb) (hC₁p : Cpass ≤ C₁)
    (hC₁a : Ca ≤ C₁) (hC₁1 : 1 ≤ C₁) (hC₁C : C₁ ≤ C)
    (hCsize : Real.exp (C₁ * T) * (Cb * ocEpsilon q Λ m₀ ^ (-(iterZ α q s K)) * (C₁ * Ca) +
      C₁ * Ca * TP) ≤ C)
    (hfloor : ∀ j, mT ≤ j → CI * ocEpsilon q Λ j ^ (q * min (ocDelta α q / 4) τe) ≤ 1 / 8)
    (hsumg : ∀ n, ∑ k ∈ Finset.Ioc m₀ n, (ocEpsilon q Λ (k - 1) ^ (5 * succEta0 α q s / 4) +
      ocEpsilon q Λ (k - 1) ^ ocMuS α q s + ocEpsilon q Λ (k - 1) ^ (ocDelta α q - 2 * σ₀)) ≤ T)
    (hsumP : ∀ n, ∑ k ∈ Finset.Ioc m₀ n, ocEpsilon q Λ (k - 1) ^ Pacc ≤ TP)
    (hamp : CascadeAmplitudeData α s q ζ Λ φ₀ hφ₀ bw t₀ T₀ r₀ D₀ τe Q H J N p nk Naux Nout Kres
      npad sX sZ σ₀ Ce kS kI CI Cw j₀ CQ Cp Ca m₀)
    (hbot : CascadeBottomData α s q ζ Λ K kI.cr Cb mB) :
    CascadeFamiliesData α s q ζ Λ φ₀ hφ₀ bw K Pacc t₀ T₀ r₀ D₀ τe Q H J N p nk Naux Nout Kres npad
      sX sZ σ₀ Ce kS kI CI Cw j₀ Cpass CQ Cp C m₀ := by
  intro D hα hq' hΛ' hζ
  subst hα hq' hΛ' hζ
  intro hΦ M hκ hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf htS hT₀' hgen hmol hm₀n
    hnM stage ext hist st tp Preg hframe hpass f
  have hε : ∀ k, 0 < D.eps k ∧ D.eps k ≤ 1 := fun k =>
    ⟨(Scales.epsilon_basic (m := k) hq.1 hΛ).1, (Scales.epsilon_basic (m := k) hq.1 hΛ).2.1⟩
  obtain ⟨hlev, hcas, hinv, hhs, -⟩ := hframe.2.2.2.2.1 n hm₀n.le le_rfl
  have hstn : st n ≤ tf := by
    rw [hframe.2.2.1]
    linarith
  have hκn : 0 < D.κ n := CycleReference.bandChain_pos (by omega) hζf hκ hnM.le
  have hD2 : 2 ≤ succSchedD D₀ N p (H + 1) := by
    change 2 ≤ succSchedD D₀ N p H + 2 * N + 4 * p + 4
    omega
  have hiota : 0 ≤ law.iota := by
    rw [hlaw.2.2.1]
    linarith
  have hamp' : AmplitudeAt law (succProvParams D Cw kI.cr σ₀ (succEta0 D.α D.q s) N p) seedK
      freshK φ₀ hφ₀ p Q Ca n m₀ tf stage hist st tp Preg :=
    hamp D rfl rfl rfl rfl hΦ M hκ hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf htS
      hT₀' hgen hm₀n hnM stage ext hist st tp Preg hframe
  have hbot' : BottomAt law (stage m₀) (m₀ + 1) K Naux s kI.cr Cb (D.eps m₀)
      (iterZ D.α D.q s K) := fun Yn a B hc hp hl hB =>
    hbot D rfl rfl rfl rfl M hκ law hiota (m₀ + 1) hmB (by omega) (stage m₀) Naux hNaux Yn a B hc
      hp hl hB
  exact cascadeOutput_of_parts law (succProvParams D Cw kI.cr σ₀ (succEta0 D.α D.q s) N p)
    (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 D.α D.q s)) seedK freshK φ₀ hφ₀ Mnat kI CI
    τe Kres (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card p N (succSchedR r₀ J H)
    sX sZ K Naux s (succEta0 D.α D.q s) (ocMuS D.α D.q s) (ocDelta D.α D.q - 2 * σ₀) Pacc Q CQ Cp
    Cpass Ca Cb (iterZ D.α D.q s K) T TP C₁ C kI.cr kI.c₀ seed n m₀ tS t₀ tf stage ext hist st tp
    Preg (by omega) hm₀n hε hCa hCb hC₁p hC₁a hC₁1 hC₁C hCsize (hsumg n) (hsumP n) hframe hpass
    (fun f => stageSol_exists law (succProvParams D Cw kI.cr σ₀ (succEta0 D.α D.q s) N p)
      (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 D.α D.q s)) seedK freshK φ₀ hφ₀ Mnat kI
      (hist n) tf _ _ seed (stage n) n hlev hinv hgen.2.1 hcas hHprod hq.1 hΛ (by omega) (by omega)
      (by rw [hterm]; exact hnM.le) hbw hκn hc₀ hc₀1 hD2 (hfloor (n - 1) (by omega)) (st n) hhs
      hstn f)
    hamp' hbot' f

/-- **The families of the cascade** from the bottom bound. -/
theorem cascadeFamilies_of_bottom (hbot : CascadeBottomStatement) (α s : ℝ) (hα₀ : 0 < α)
    (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : CascadeFamiliesStatement α s q ζ := by
  classical
  obtain ⟨Λa, hΛa, ha⟩ := cascadeAmplitude α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λb, hΛb, hb⟩ := hbot α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max Λa Λb, by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨ca, hca, ha⟩ := ha Λ (by omega)
  have hb := hb Λ (by omega)
  refine ⟨min ca 1, lt_min hca one_pos, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc t₀ T₀ hK hPacc ht₀ hT₀
    r₀ D₀ τe lamE σE hτe hlamE hσE Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a σ hsched npad
  obtain ⟨SX, SZ, ha⟩ := ha φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc t₀ T₀ hK
    hPacc ht₀ hT₀ r₀ D₀ τe lamE σE hτe hlamE hσE Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a
    σ hsched npad
  refine ⟨SX, SZ, 0, ?_⟩
  intro sX sZ hSX hSZ Ce kS hCe hc₀ hc₀upper hcr hcrupper hσf hlamC halloc _ _ _ _
  obtain ⟨thr, CH, Υ, hCH, hΥ, ha⟩ := ha sX sZ hSX hSZ Ce kS hCe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC halloc
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, ha⟩ := ha kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart Cpass CQ Cp
  obtain ⟨Ca, ma, hCa, ha⟩ := ha CI Cw j₀ hledger hstart CQ Cp
  have hkc : kI.c₀ = kS.c₀ := hkI.1
  have hkr : kI.cr = kS.cr := hkI.2.1
  have hHprod : kI.Hprod = kI.G0 + H + 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      h, _⟩ := hkI
    exact h
  obtain ⟨Cb0, mB, hb⟩ := hb K (by omega) kI.cr (hkr ▸ hcr) (hkr ▸ hcrupper)
  have hη := succEta0_pos_of_admissible hα₀ hs₀ hq
  have hμ := ocMuS_pos_of_admissible hα₀ hs₀ hq
  have hδ := ocDelta_pos_of_admissible hα₀ hq
  have hw := cascade_width_exponent_pos hα₀ hq hsched
  obtain ⟨T₁, hT₁, hS₁⟩ := scale_sum_tail (Λ := Λ) (p := 5 * succEta0 α q s / 4) hq.1 h128
    (by linarith)
  obtain ⟨T₂, hT₂, hS₂⟩ := scale_sum_tail (Λ := Λ) (p := ocMuS α q s) hq.1 h128 hμ
  obtain ⟨T₃, hT₃, hS₃⟩ := scale_sum_tail (Λ := Λ) (p := ocDelta α q - 2 * σ₀) hq.1 h128 hw
  obtain ⟨TP, hTP, hSP⟩ := scale_sum_tail (Λ := Λ) (p := Pacc) hq.1 h128 hPacc
  have hq0 : 0 < q := zero_lt_one.trans hq.1
  have hδ4 : 0 < ocDelta α q / 4 := by linarith
  obtain ⟨mT, hmT⟩ := scale_floor (Λ := Λ) (p := q * min (ocDelta α q / 4) τe) (W := CI)
    (η := 1 / 8) hq.1 h128 (mul_pos hq0 (lt_min hδ4 hτe)) (by norm_num)
  refine ⟨max (max ma mB) (max (mT + 1) (max j₀ 1)), ?_⟩
  intro m₀ hm₀
  have hma : ma ≤ m₀ := ((le_max_left _ _).trans (le_max_left _ _)).trans hm₀
  have hmB : mB ≤ m₀ := ((le_max_right _ _).trans (le_max_left _ _)).trans hm₀
  have hmT' : mT + 1 ≤ m₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hm₀
  have hj₀ : j₀ ≤ m₀ :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hm₀
  have hm1 : 1 ≤ m₀ :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hm₀
  refine ⟨max (max (max Cpass Ca) 1) (Real.exp (max (max Cpass Ca) 1 * (T₁ + T₂ + T₃)) *
      (max Cb0 0 * ocEpsilon q Λ m₀ ^ (-(iterZ α q s K)) * (max (max Cpass Ca) 1 * Ca) +
        max (max Cpass Ca) 1 * Ca * TP)),
    lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  exact cascadeFamiliesData_of_parts hq hζ h128 hbw ht₀ hη (hkc ▸ hc₀)
    (hkc ▸ (hc₀upper.trans (min_le_right _ _))) hHprod
    (by have := hsched.2.2.2.2.2.1.1; omega) Cpass CQ Cp Ca (max Cb0 0) (T₁ + T₂ + T₃) TP
    (max (max Cpass Ca) 1) _ mB mT m₀ (hmB.trans (Nat.le_succ _)) hmT' hj₀ hm1 hCa
    (le_max_right _ _) ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _) (le_max_left _ _)
    (le_max_right _ _) hmT
    (fun n => by
      have h1 := hS₁ m₀ n hm1
      have h2 := hS₂ m₀ n hm1
      have h3 := hS₃ m₀ n hm1
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      linarith)
    (fun n => hSP m₀ n hm1) (ha m₀ hma) (hb _ (le_max_left _ _))

end AVRegularity.IterationPassage.Cascade
end
end
end

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.IterationPassage.Passage
namespace AVRegularity.IterationPassage.Cascade

/-! **`iteration_cascade_of_schedule` from the ingredients of the iteration argument**.

`iteration_cascade_of_schedule_of_lane_ingredients`: the exact statement
`IterationCascadeOfScheduleStatement` from

* the statements `preservation_successor` and `successor_bill` of the preservation argument;
* the six profile ingredients of one passage (`Passage/Profiles/Statements.lean`);
* the families of the cascade, `CascadeFamiliesStatement` (`Cascade/Statements.lean`).
* the families of the cascade, `CascadeFamiliesStatement` (`Cascade/Statements.lean`).

The run of the cascade, the passage assembly and every producer are discharged. The
statement `iteration_cascade` follows by `iteration_cascade_of_ingredients`
(`IterationPassage/Assembly/IterationCascadeOfIngredients.lean`). -/

/-- **`iteration_cascade_of_schedule`** from the ingredients of the argument. -/
theorem iteration_cascade_of_schedule_of_lane_ingredients
    (hps0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → SuccessorBillStatement α s q ζ)
    (hsm : SmoothRepOfHigherStatement)
    (hr0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageProfilesRegularStatement α s q ζ)
    (hc0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageRetainedCovarianceStatement α s q ζ)
    (hl0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageRetainedLiftStatement α s q ζ)
    (hd0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageDiscardedProfilesStatement α s q ζ)
    (he0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageErrorProfileStatement α s q ζ)
    (hfam : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → CascadeFamiliesStatement α s q ζ) :
    IterationPassage.Assembly.IterationCascadeOfScheduleStatement :=
  iteration_cascade_of_schedule_of_passage
    (iteration_passage_of_profile_ingredients hps0 hbill hsm hr0 hc0 hl0 hd0 he0) hfam

end AVRegularity.IterationPassage.Cascade
end
end

section
section
/-! **`iteration_cascade_of_schedule` from the leaves of the iteration argument**.

`iteration_cascade_of_schedule_of_leaves`: the exact statement
`IterationCascadeOfScheduleStatement` from

* the statements `preservation_successor` and `successor_bill` of the preservation argument;
* the six profile ingredients of one passage;
* the bottom bound of the cascade, `CascadeBottomStatement`.

The families of the cascade are `cascadeFamilies_of_bottom` (`Cascade/FamiliesAssembly.lean`). The
shared Sobolev-to-profile bound is an ingredient of the profile ingredients and the bottom bound, not of this
assembly. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.IterationPassage.Passage

namespace AVRegularity.IterationPassage.Cascade

/-- **`iteration_cascade_of_schedule`** from the leaves of the argument. -/
theorem iteration_cascade_of_schedule_of_leaves
    (hps0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → SuccessorBillStatement α s q ζ)
    (hsm : SmoothRepOfHigherStatement)
    (hr0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageProfilesRegularStatement α s q ζ)
    (hc0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageRetainedCovarianceStatement α s q ζ)
    (hl0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageRetainedLiftStatement α s q ζ)
    (hd0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageDiscardedProfilesStatement α s q ζ)
    (he0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageErrorProfileStatement α s q ζ)
    (hbot : CascadeBottomStatement) :
    IterationPassage.Assembly.IterationCascadeOfScheduleStatement :=
  iteration_cascade_of_schedule_of_lane_ingredients hps0 hbill hsm hr0 hc0 hl0 hd0 he0
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
      cascadeFamilies_of_bottom hbot α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

end AVRegularity.IterationPassage.Cascade
end
end

section
/-! **The statements of the iteration argument from the two preservation statements**.

All the other leaves of the iteration argument are proved and discharged (`smoothRepOfHigher`,
`passageProfilesRegular`, `passageRetainedCovariance`, `passageRetainedLift`,
`passageDiscardedProfiles`, `passageErrorProfile` and `cascadeBottom`, with the Sobolev-to-profile bound inside).
What remains are the two statements `preservation_successor` and `successor_bill` of the preservation argument.

`iteration_passage_of_open_leaves` and `iteration_cascade_of_schedule_of_open_leaves` are the
exact statements from these two. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.IterationPassage.Passage

namespace AVRegularity.IterationPassage.Cascade

/-- **`iteration_passage`** from its open leaves. -/
theorem iteration_passage_of_open_leaves
    (hps0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        SuccessorBillStatement α s q ζ) :
    IterationPassage.Assembly.IterationPassageStatement :=
  iteration_passage_of_profile_ingredients hps0 hbill smoothRepOfHigher
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => passageProfilesRegular α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
      passageRetainedCovariance α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => passageRetainedLift α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
      passageDiscardedProfiles α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => passageErrorProfile α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

/-- **`iteration_cascade_of_schedule`** from its open leaves. -/
theorem iteration_cascade_of_schedule_of_open_leaves
    (hps0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        SuccessorBillStatement α s q ζ) :
    IterationPassage.Assembly.IterationCascadeOfScheduleStatement :=
  iteration_cascade_of_schedule_of_leaves hps0 hbill smoothRepOfHigher
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => passageProfilesRegular α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
      passageRetainedCovariance α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => passageRetainedLift α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
      passageDiscardedProfiles α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => passageErrorProfile α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    cascadeBottom

end AVRegularity.IterationPassage.Cascade
end
end
end
end
