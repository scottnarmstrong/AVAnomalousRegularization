-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.CoarseEnergy.PartBTransfer
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.EntryWeakAssembly.MassRecursion
import AVRegularity.Proofs.WeakGen.Reduction.PassageEnergy
import Mathlib.Data.Int.Star

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal Classical
namespace AVRegularity.Providers.WeakGen.Residual.PartB

/-! **Coarse readout energy, Part B: the children's classical energies and the square root**.

* `partB_child_factorial`, `partB_child_grad`: the sum over the children of `u_c` times the
  classical factorial (gradient) norms of classical representatives is at most `ofReal` of the
  corresponding sum of `TorusHk` factorial (gradient) norms (`partB_factorial_le`, `partB_grad_le`).
* `partB_sqrt_step`: the square root of a bound `#V · (n · 2Q)`.
-/

theorem partB_child_factorial {C : Type} [Fintype C] {K : C → ℕ} (ρ : ℝ) (k r : ℕ) (hkr : k ≤ r)
    (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) (P : C → Prop) [∀ c, Decidable (P c)]
    (U : ∀ c, TorusHk (K c) ℝ) (a : C → Vec 2 → ℝ) (hrep : ∀ c, IsClassicalRep (U c) (a c) r) :
    (∑ c, if P c then ENNReal.ofReal (u c) * classicalFactorialSq ρ k (a c) else 0) ≤
      ENNReal.ofReal (∑ c, if P c then u c * factorialNormSq ρ (U c).val else 0) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => by
    split_ifs
    · exact mul_nonneg (hu c) (factorialNormSq_nonneg ρ _)
    · exact le_rfl)]
  refine Finset.sum_le_sum fun c _ => ?_
  split_ifs
  · rw [ENNReal.ofReal_mul (hu c)]
    exact mul_le_mul' le_rfl (partB_factorial_le (hrep c) hkr ρ)
  · simp

theorem partB_child_grad {C : Type} [Fintype C] {K : C → ℕ} (ρ : ℝ) (k r : ℕ) (hkr : k + 1 ≤ r)
    (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) (P : C → Prop) [∀ c, Decidable (P c)]
    (W : ∀ c, TorusHk (K c + 1) ℝ) (a : C → Vec 2 → ℝ)
    (hrep : ∀ c, IsClassicalRep (W c) (a c) r) :
    (∑ c, if P c then ENNReal.ofReal (u c) * classicalGradFactorialSq ρ k (a c) else 0) ≤
      ENNReal.ofReal (∑ c, if P c then u c * gradFactorialNormSq ρ (W c).val else 0) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => by
    split_ifs
    · exact mul_nonneg (hu c) (CycleComparison.Coarse.gradFactorialNormSq_nonneg ρ _)
    · exact le_rfl)]
  refine Finset.sum_le_sum fun c _ => ?_
  split_ifs
  · rw [ENNReal.ofReal_mul (hu c)]
    exact mul_le_mul' le_rfl (partB_grad_le (hrep c) hkr ρ)
  · simp

/-- The square root of the transfer bound. -/
theorem partB_sqrt_step (S : ℝ≥0∞) (cV n : ℕ) (hc : cV ≤ n) (Z : ℝ) (hZ : 0 ≤ Z)
    (hS : S ≤ (cV : ℝ≥0∞) * ((n : ℝ≥0∞) * (2 * ENNReal.ofReal Z))) :
    S ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt (2 * n * n * Z)) := by
  have h1 : S ≤ ENNReal.ofReal (2 * n * n * Z) := by
    refine hS.trans ?_
    have hcn : (cV : ℝ≥0∞) ≤ n := by exact_mod_cast hc
    calc (cV : ℝ≥0∞) * ((n : ℝ≥0∞) * (2 * ENNReal.ofReal Z)) ≤
          (n : ℝ≥0∞) * ((n : ℝ≥0∞) * (2 * ENNReal.ofReal Z)) := mul_le_mul' hcn le_rfl
      _ = ENNReal.ofReal (2 * n * n * Z) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity)]
          simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
          ring
  calc S ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (2 * n * n * Z)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (2 * n * n * Z)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.sqrt_eq_rpow]

/-- The hypothesis `hQ` of the transfer, from the `TorusHk` bounds of the families. -/
theorem partB_hQ {C : Type} [Fintype C] {K : C → ℕ} (ρ κ : ℝ) (k : ℕ) (I : Set ℝ)
    (hIm : MeasurableSet I) (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) (P : C → Prop) [∀ c, Decidable (P c)]
    (U : ∀ c, ℝ → TorusHk (K c) ℝ) (W : ∀ c, ℝ → TorusHk (K c + 1) ℝ)
    (a : ℝ → C → Vec 2 → ℝ)
    (hrepU : ∀ t ∈ I, ∀ c, IsClassicalRep (U c t) (a t c) (k + 1))
    (htr : ∀ c, ∀ᵐ τ ∂(volume.restrict I), truncateTorusHk (Nat.le_succ (K c)) (W c τ) = U c τ)
    (hKk : ∀ c, k + 1 ≤ K c) (Q : ℝ≥0∞)
    (hA : ∀ t ∈ I, ENNReal.ofReal (∑ c, if P c then u c * factorialNormSq ρ (U c t).val else 0) +
        ENNReal.ofReal (κ / 2) * ∫⁻ τ in I, ENNReal.ofReal
          (∑ c, if P c then u c * gradFactorialNormSq ρ (W c τ).val else 0) ≤ Q) :
    ∀ t ∈ I, (∑ c, if P c then ENNReal.ofReal (u c) * classicalFactorialSq ρ k (a t c) else 0) +
        ENNReal.ofReal (κ / 2) * ∫⁻ τ in I,
          (∑ c, if P c then ENNReal.ofReal (u c) * classicalGradFactorialSq ρ k (a τ c)
            else 0) ≤ Q := by
  intro t ht
  refine le_trans (add_le_add (partB_child_factorial ρ k (k + 1) (Nat.le_succ k) u hu P
    (fun c => U c t) (a t) (hrepU t ht)) (mul_le_mul' le_rfl ?_)) (hA t ht)
  refine lintegral_mono_ae ?_
  have hall := ae_all_iff.2 htr
  filter_upwards [hall, ae_restrict_mem hIm] with τ hτ hτI
  refine partB_child_grad ρ k (k + 1) le_rfl u hu P (fun c => W c τ) (a τ) (fun c => ?_)
  refine partB_rep_of_truncate (Nat.le_succ (K c)) (hKk c) (W c τ) (a τ c) ?_
  rw [hτ c]
  exact hrepU τ hτI c

/-- The generic energy bound: the classical strong energy of a weighted sum of the children. -/
theorem partB_energy_generic (hCS : WeakReadoutCSStatement)
    {V C : Type} [Fintype V] [Fintype C]
    (sel : C → V → Prop) (P : C → Prop) [∀ c v, Decidable (sel c v)] [∀ c, Decidable (P c)]
    (hsel : ∀ c v, sel c v → P c)
    (ρ B : ℝ) (π : V → ℝ) (I : Set ℝ) (hIm : MeasurableSet I) (hI : I.Nonempty) (k : ℕ)
    (a : ℝ → C → Vec 2 → ℝ) (rc u : C → ℝ) (n : ℕ)
    (hπ : ∀ v, 0 ≤ π v)
    (hcard : ∀ v, (Finset.univ.filter fun c => sel c v).card ≤ n)
    (hw : ∀ v c, sel c v → (π v)⁻¹ * rc c ^ 2 ≤ u c)
    (hd : ∀ t ∈ I, ∀ c, ContDiff ℝ (k + 1 : ℕ) (a t c)) (Q : ℝ≥0∞) (Z : ℝ) (hZ : 0 ≤ Z)
    (hQZ : Q ≤ ENNReal.ofReal Z) (hcV : Fintype.card V ≤ n)
    (hQ : ∀ t ∈ I,
      (∑ c, if P c then ENNReal.ofReal (u c) * classicalFactorialSq ρ k (a t c) else 0) +
        ENNReal.ofReal (B / 2) * ∫⁻ τ in I,
          (∑ c, if P c then ENNReal.ofReal (u c) * classicalGradFactorialSq ρ k (a τ c)
            else 0) ≤ Q) :
    (∑ v, ENNReal.ofReal (π v)⁻¹ *
      ((⨆ t ∈ I, classicalFactorialSq ρ k (fun x => ∑ c, if sel c v then rc c * a t c x else 0)) +
        ENNReal.ofReal B * ∫⁻ t in I,
          classicalGradFactorialSq ρ k (fun x => ∑ c, if sel c v then rc c * a t c x else 0))) ^
      (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt (2 * n * n * Z)) :=
  partB_sqrt_step _ _ n hcV Z hZ
    ((partB_strongEnergy_sum_le hCS sel P hsel ρ B π I hIm hI k a rc u n hπ hcard hw hd Q hQ).trans
      (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hQZ))))

/-! **Coarse readout energy, Part B: the instance lemmas**.

On a passage instance: clauses 1 and 2 (smoothness and joint continuity of the classical
representative), the energy of the coarse readout (clause 3) from the energy at a high reserve
(`WeakCoarseHighEnergyAt`), and the energy of the length-`R_w` readout (clause 4) from the raw
frontier estimate (`WeakCoarseRawFrontierAt`). Each is conditional on the statements
`WeakReadoutCSStatement`, `WeakReadoutMassStatement` and the counts.
-/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

theorem partB_mass_pos (c : WeakPassageInstance plan R) (v : Comp) :
    0 < weakMass c.D A.Nw A.Jw A.η₀ v := by
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge B).trans c.base_ge)
  exact weakMass_pos c.D _ _ _ A.Nw_pos A.Jw_pos
    (fun _ => Construction.Stream.ocEpsilon_pos hΛ) v

theorem partB_eps_nonneg (c : WeakPassageInstance plan R) (j : ℕ) : 0 ≤ c.D.eps j := by
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge B).trans c.base_ge)
  exact (Construction.Stream.ocEpsilon_pos hΛ (n := j)).le

/-- Clauses 1 and 2 of (iv). -/
theorem partB_claim12 (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (m k : ℕ)
    (hk : k + 3 ≤ R.Kw + m)
    (Uhi : ∀ i, WeakStageFamily (weakPassageRawSetting c) m i)
    (Whi : ∀ i, WeakStageLift (weakPassageRawSetting c) m i) (i : ℕ)
    (hpass : WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi i)
    (a : ℝ → CompIn (c.stage (i - 1)).comps → Vec 2 → ℝ)
    (hrep : ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), IsClassicalRep (Uhi (i - 1) v t) (a t v) (k + 1)) :
    (∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), ∀ v', ContDiff ℝ ((k + 1 : ℕ) : ℕ∞) (a t v')) ∧
    (∀ v' n, n ≤ k + 1 → ∀ w : DerivativeWord2 n,
      ContinuousOn (fun p : ℝ × Vec 2 => orderedDerivative w (a p.1 v') p.2)
        (Set.Icc (r.tq i) (r.a + A.T₀) ×ˢ Set.univ)) := by
  refine ⟨fun t ht v' => ?_, fun v' n hn w => ?_⟩
  · have := (hrep v' t ht).2.1
    exact_mod_cast this
  · have hK : R.Kw + m ≤ weakReductionReserve R m v'.1 := Nat.le_add_right _ _
    exact partB_derivative_continuousOn (K := weakReductionReserve R m v'.1) (r := k + 1)
      (by omega) _ (Uhi (i - 1) v') (hpass.1 v') (a · v') (fun t ht => hrep v' t ht) hn w

/-- The reserves of the high family are above `k + 3`. -/
theorem partB_reserve_ge (m k : ℕ) (hk : k + 3 ≤ R.Kw + m) (c : Comp) :
    k + 1 ≤ weakReductionReserve R m c := by
  have : R.Kw + m ≤ weakReductionReserve R m c := Nat.le_add_right _ _
  omega

/-- **Clause 3**: the energy of the coarse readout, from the high-reserve energy
`WeakCoarseHighEnergyAt`. -/
theorem partB_ordinary_energy (hCS : WeakReadoutCSStatement) (hMass : WeakReadoutMassStatement plan)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (m k : ℕ) (hk : k + 3 ≤ R.Kw + m)
    (Uhi : ∀ i, WeakStageFamily (weakPassageRawSetting c) m i)
    (Whi : ∀ i, WeakStageLift (weakPassageRawSetting c) m i) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (hpass : WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi i)
    (aU : ℝ → CompIn (c.stage (i - 1)).comps → Vec 2 → ℝ)
    (hrep : ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      IsClassicalRep (Uhi (i - 1) v t) (aU t v) (k + 1))
    (n : ℕ) (hcV : Fintype.card (CompIn (c.stage i).comps) ≤ n)
    (hfib : ∀ v : Comp, (Finset.univ.filter
      fun v' : CompIn (c.stage (i - 1)).comps => compParent i v'.1 = v).card ≤ n)
    (CA Φ : ℝ) (hCA : 0 ≤ CA)
    (hA : ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      ENNReal.ofReal (massNormSq (plan.radius R * c.D.eps (i - 1))
          (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (Uhi (i - 1) v t).val)) +
        ENNReal.ofReal (c.D.κ c.M / 2) *
          ∫⁻ τ in Set.Icc (r.tq i) (r.a + A.T₀),
            ENNReal.ofReal (massGradNormSq (plan.radius R * c.D.eps (i - 1))
              (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
              (fun v => (Whi (i - 1) v τ).val)) ≤
      ENNReal.ofReal (CA * Φ ^ 2)) :
    classicalStrongEnergy (plan.radius R * c.D.eps (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (Set.Icc (r.tq i) (r.a + A.T₀)) k
        (weakResidualReadout i A.η₀ (c.stage i) (c.stage (i - 1)) aU) ≤
      ENNReal.ofReal (Real.sqrt (2 * n * n * (CA * Φ ^ 2))) := by
  have hIm : MeasurableSet (Set.Icc (r.tq i) (r.a + A.T₀)) := measurableSet_Icc
  have hI : (Set.Icc (r.tq i) (r.a + A.T₀)).Nonempty :=
    ⟨r.tq i, le_rfl, (weak_quiet_window c r i hi hit).2.1⟩
  have htr : ∀ v, ∀ᵐ τ ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))),
      truncateTorusHk (Nat.le_succ (weakReductionReserve R m v.1))
        (Whi (i - 1) v τ) = Uhi (i - 1) v τ := hpass.2.2.1
  have hQ := partB_hQ (K := fun v : CompIn (c.stage (i - 1)).comps =>
      weakReductionReserve R m v.1) (plan.radius R * c.D.eps (i - 1)) (c.D.κ c.M) k
    (Set.Icc (r.tq i) (r.a + A.T₀)) hIm
    (fun v => (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹)
    (fun v => inv_nonneg.2 (partB_mass_pos c v.1).le) (fun _ => True)
    (fun v t => Uhi (i - 1) v t) (fun v t => Whi (i - 1) v t) aU (fun t ht v => hrep v t ht) htr
    (fun v => partB_reserve_ge m k hk v.1) (ENNReal.ofReal (CA * Φ ^ 2))
    (fun t ht => by simpa [massNormSq, massGradNormSq] using hA t ht)
  exact partB_energy_generic hCS (V := CompIn (c.stage i).comps)
    (C := CompIn (c.stage (i - 1)).comps) (fun c' v => compParent i c'.1 = v.1) (fun _ => True)
    (fun _ _ _ => trivial) (plan.radius R * c.D.eps (i - 1)) (c.D.κ c.M)
    (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) _ hIm hI k aU
    (fun c' => (c.D.eps (i - 1) ^ A.η₀) ^ (compWord i c'.1).length)
    (fun c' => (weakMass c.D A.Nw A.Jw A.η₀ c'.1)⁻¹) n
    (fun v => (partB_mass_pos c v.1).le) (fun v => by convert hfib v.1)
    (fun v c' hs => by rw [← hs]; exact (hMass c i c'.1).1)
    (fun t ht c' => (hrep c' t ht).2.1.of_le le_rfl) (ENNReal.ofReal (CA * Φ ^ 2)) (CA * Φ ^ 2)
    (mul_nonneg hCA (sq_nonneg _)) le_rfl hcV hQ

/-- **Clause 4**: the energy of the length-`R_w` readout, from the raw frontier estimate
`WeakCoarseRawFrontierAt`. -/
theorem partB_frontier_energy (hCS : WeakReadoutCSStatement)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (m k : ℕ) (hk : k + 3 ≤ R.Kw + m)
    (Uhi : ∀ i, WeakStageFamily (weakPassageRawSetting c) m i)
    (Whi : ∀ i, WeakStageLift (weakPassageRawSetting c) m i) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (hpass : WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi i)
    (aU : ℝ → CompIn (c.stage (i - 1)).comps → Vec 2 → ℝ)
    (hrep : ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      IsClassicalRep (Uhi (i - 1) v t) (aU t v) (k + 1))
    (n : ℕ) (hcV : Fintype.card (CompIn (c.stage i).comps) ≤ n)
    (hfib : ∀ v : Comp, (Finset.univ.filter
      fun v' : CompIn (c.stage (i - 1)).comps => compParent i v'.1 = v).card ≤ n)
    (Z : ℝ) (hZ : 0 ≤ Z)
    (hF : ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      ENNReal.ofReal (∑ v : CompIn (c.stage (i - 1)).comps,
          if (compWord i v.1).length = A.Rw then
            (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v.1))⁻¹ *
              ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2 *
              factorialNormSq (plan.radius R * c.D.eps (i - 1)) (Uhi (i - 1) v t).val
          else 0) +
        ENNReal.ofReal (c.D.κ c.M / 2) *
          ∫⁻ τ in Set.Icc (r.tq i) (r.a + A.T₀),
            ENNReal.ofReal (∑ v : CompIn (c.stage (i - 1)).comps,
              if (compWord i v.1).length = A.Rw then
                (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v.1))⁻¹ *
                  ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2 *
                  gradFactorialNormSq (plan.radius R * c.D.eps (i - 1)) (Whi (i - 1) v τ).val
              else 0) ≤ ENNReal.ofReal Z) :
    classicalStrongEnergy (plan.radius R * c.D.eps (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (Set.Icc (r.tq i) (r.a + A.T₀)) k
        (fun t x v => weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (aU t) v x) ≤
      ENNReal.ofReal (Real.sqrt (2 * n * n * Z)) := by
  have hIm : MeasurableSet (Set.Icc (r.tq i) (r.a + A.T₀)) := measurableSet_Icc
  have hI : (Set.Icc (r.tq i) (r.a + A.T₀)).Nonempty :=
    ⟨r.tq i, le_rfl, (weak_quiet_window c r i hi hit).2.1⟩
  have htr : ∀ v, ∀ᵐ τ ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))),
      truncateTorusHk (Nat.le_succ (weakReductionReserve R m v.1))
        (Whi (i - 1) v τ) = Uhi (i - 1) v τ := hpass.2.2.1
  have hQ := partB_hQ (K := fun v : CompIn (c.stage (i - 1)).comps =>
      weakReductionReserve R m v.1) (plan.radius R * c.D.eps (i - 1)) (c.D.κ c.M) k
    (Set.Icc (r.tq i) (r.a + A.T₀)) hIm
    (fun v => (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v.1))⁻¹ *
      ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2)
    (fun v => mul_nonneg (inv_nonneg.2 (partB_mass_pos c _).le) (sq_nonneg _))
    (fun v => (compWord i v.1).length = A.Rw)
    (fun v t => Uhi (i - 1) v t) (fun v t => Whi (i - 1) v t) aU (fun t ht v => hrep v t ht) htr
    (fun v => partB_reserve_ge m k hk v.1) (ENNReal.ofReal Z) hF
  have hE0 : 0 ≤ c.D.eps (i - 1) ^ A.η₀ := Real.rpow_nonneg (partB_eps_nonneg c _) _
  exact partB_energy_generic hCS (V := CompIn (c.stage i).comps)
    (C := CompIn (c.stage (i - 1)).comps)
    (fun c' v => compParent i c'.1 = v.1 ∧ (compWord i c'.1).length = A.Rw)
    (fun v => (compWord i v.1).length = A.Rw)
    (fun _ _ hs => hs.2) (plan.radius R * c.D.eps (i - 1)) (c.D.κ c.M)
    (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) _ hIm hI k aU
    (fun _ => (c.D.eps (i - 1) ^ A.η₀) ^ A.Rw)
    (fun c' => (weakMass c.D A.Nw A.Jw A.η₀ (compParent i c'.1))⁻¹ *
      ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2) n
    (fun v => (partB_mass_pos c v.1).le)
    (fun v => le_trans (Finset.card_le_card (t := Finset.univ.filter
      fun c' : CompIn (c.stage (i - 1)).comps => compParent i c'.1 = v.1) (fun c' hc' => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc' ⊢
      exact hc'.1)) (by convert hfib v.1))
    (fun v c' hs => by
      obtain ⟨h1, -⟩ := hs
      rw [h1])
    (fun t ht c' => (hrep c' t ht).2.1.of_le le_rfl) (ENNReal.ofReal Z) Z hZ le_rfl hcV hQ
end

end AVRegularity.Providers.WeakGen.Residual.PartB
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! **Coarse readout energy, Part B: the assembly**.

`weakCoarseReadoutEnergy_core`: the body of the coarse readout energy statement (iv), from the
energy at a high reserve (`WeakCoarseHighEnergyAt`), the raw frontier estimate
(`WeakCoarseRawFrontierAt`), the counts, and the statements `WeakReadoutCSStatement`,
`WeakReadoutMassStatement`, `WeakCoarseFamilyRepStatement`.
-/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction PartB

theorem partB_sqrt_gain (K x e p Φ : ℝ) (hK : 0 ≤ K) (hx : 0 ≤ x) (hΦ : 0 ≤ Φ) (hp : p = e * 2) :
    Real.sqrt (K * x ^ p * Φ ^ 2) = Real.sqrt K * x ^ e * Φ := by
  have h1 : x ^ p = (x ^ e) ^ 2 := by
    rw [hp]
    exact_mod_cast Real.rpow_mul_natCast hx e 2
  have hxe : 0 ≤ x ^ e := Real.rpow_nonneg hx e
  rw [h1, show K * (x ^ e) ^ 2 * Φ ^ 2 = K * (x ^ e * Φ) ^ 2 by ring,
    Real.sqrt_mul hK, Real.sqrt_sq (mul_nonneg hxe hΦ)]
  ring

theorem partB_sqrt_plain (K Φ : ℝ) (hK : 0 ≤ K) (hΦ : 0 ≤ Φ) :
    Real.sqrt (K * Φ ^ 2) = Real.sqrt K * Φ := by
  rw [Real.sqrt_mul hK, Real.sqrt_sq hΦ]

/-- **The body of (iv) at explicit constants**: from the high-reserve energy at `CA`, the raw
frontier estimate at `CF` and the counts at `n`, the four clauses hold with the constant
`√(2n²C_A) + √(2n²C_F)`. -/
theorem weakCoarseReadoutEnergy_core {plan : WeakPassagePlan}
    {kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ}
    (hok : WeakCoarseReadoutPlanOK plan kOf)
    (hCS : WeakReadoutCSStatement) (hMass : WeakReadoutMassStatement plan)
    (hRep : WeakCoarseFamilyRepStatement plan kOf)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (CA CF : ℝ) (n : ℕ) (hCA : 0 ≤ CA) (hCF : 0 ≤ CF)
    (hA : WeakCoarseHighEnergyAt plan R (weakEntryMmax R) CA)
    (hF : WeakCoarseRawFrontierAt plan R (weakEntryMmax R) CF)
    (hn : ∀ (c : WeakPassageInstance plan R) (i : ℕ), c.M < i → i ≤ c.M + A.Jw →
      Fintype.card (CompIn (c.stage i).comps) ≤ n ∧
      ∀ v : Comp, (Finset.univ.filter
        fun v' : CompIn (c.stage (i - 1)).comps => compParent i v'.1 = v).card ≤ n) :
    WeakCoarseReadoutEnergyBody plan kOf R
      (Real.sqrt (2 * n * n * CA) + Real.sqrt (2 * n * n * CF)) := by
  intro c r i hi hit h
  obtain ⟨Uhi, Whi, hpass, hvr, hval, hbound⟩ := hA c r h.start
  have hk : kOf R + 3 ≤ R.Kw + weakEntryMmax R := by
    unfold weakEntryMmax
    exact (hok.2 R).trans (Nat.add_le_add_left (Nat.add_le_add_left c.moment_ge _) _)
  have hrep := hRep R (weakEntryMmax R) le_rfl hk c r Uhi i hi hit h (hval i hi hit)
  obtain ⟨c1, c2⟩ := partB_claim12 c r (weakEntryMmax R) (kOf R) hk Uhi Whi i (hpass i hi hit)
    h.aU hrep
  have hwin := weak_quiet_window c r i hi hit
  have hΦ0 : 0 ≤ h.Φ :=
    (by unfold weightedNorm; positivity : (0 : ℝ) ≤ _).trans
      (h.mass_bound (r.tq (i + 1)) ⟨le_rfl, hwin.2.2.1.le.trans hwin.2.1⟩)
  have hcn := hn c i hi hit
  refine ⟨c1, c2, ?_, ?_⟩
  · have key := partB_ordinary_energy hCS hMass c r (weakEntryMmax R) (kOf R) hk Uhi Whi i hi hit
      (hpass i hi hit) h.aU hrep n hcn.1 hcn.2 CA h.Φ hCA
      (fun t ht => hbound i hi hit h.Φ h.mass_bound t ht)
    refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [show 2 * (n : ℝ) * n * (CA * h.Φ ^ 2) = (2 * n * n * CA) * h.Φ ^ 2 by ring,
      partB_sqrt_plain _ _ (by positivity) hΦ0]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hΦ0
  · have hx : 0 < c.D.eps c.M := by
      have hΛ : 1 ≤ c.D.Λ := by
        rw [c.base_eq]
        exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge B).trans c.base_ge)
      exact Construction.Stream.ocEpsilon_pos hΛ
    have key := partB_frontier_energy hCS c r (weakEntryMmax R) (kOf R) hk Uhi Whi i hi hit
      (hpass i hi hit) h.aU hrep n hcn.1 hcn.2
      (CF * c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw) * h.Φ ^ 2)
      (by have := Real.rpow_nonneg hx.le (4 * weakAStar B.α B.q * A.Rw); positivity)
      (fun t ht => hF c r h.start Uhi Whi (fun i h1 h2 => hpass i h1 h2) hvr hval i hi hit h.Φ
        h.mass_bound t ht)
    refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [show 2 * (n : ℝ) * n * (CF * c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw) * h.Φ ^ 2) =
      (2 * n * n * CF) * c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw) * h.Φ ^ 2 by ring,
      partB_sqrt_gain _ _ (2 * weakAStar B.α B.q * A.Rw) _ _ (by positivity) hx.le hΦ0
        (by ring)]
    have hxe : 0 ≤ c.D.eps c.M ^ (2 * weakAStar B.α B.q * A.Rw) := Real.rpow_nonneg hx.le _
    calc Real.sqrt (2 * n * n * CF) * c.D.eps c.M ^ (2 * weakAStar B.α B.q * A.Rw) * h.Φ
        = Real.sqrt (2 * n * n * CF) * (c.D.eps c.M ^ (2 * weakAStar B.α B.q * A.Rw) * h.Φ) := by
          ring
      _ ≤ (Real.sqrt (2 * n * n * CA) + Real.sqrt (2 * n * n * CF)) *
            (c.D.eps c.M ^ (2 * weakAStar B.α B.q * A.Rw) * h.Φ) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Real.sqrt_nonneg _))
            (mul_nonneg hxe hΦ0)
      _ = _ := by ring

end AVRegularity.Providers.WeakGen.Residual
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual

/-! **Coarse readout energy, Part B: the component counts**.

`weakReadoutCount_at`: the counts, at the named constant `weakReadoutCountConst`. Downward
induction along the weak construction
from the root: the stage `M + J_w - n` has level `M + J_w - n`, births of scale at least its level,
and at most `(1 + |W|)^n` components, `W = wordsUpTo (weakAlphabet N_w) R_w`. The fibre over a
parent has at most `|wordsUpTo (weakAlphabet N_w) (R_w + 1)| + 1` elements
(`readout_indexed_fiber_card_le`).
-/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction PartB

theorem partB_weakExtComps_card (m N R : ℕ) (S : Finset Comp) :
    (weakExtComps m N R S).card ≤ (1 + (wordsUpTo (weakAlphabet N) R).card) * S.card := by
  unfold weakExtComps
  calc (S ∪ (S ×ˢ wordsUpTo (weakAlphabet N) R).image fun x => succComp m x.1 x.2).card
      ≤ S.card + ((S ×ˢ wordsUpTo (weakAlphabet N) R).image fun x => succComp m x.1 x.2).card :=
        Finset.card_union_le _ _
    _ ≤ S.card + (S ×ˢ wordsUpTo (weakAlphabet N) R).card :=
        Nat.add_le_add_left Finset.card_image_le _
    _ = _ := by rw [Finset.card_product]; ring

theorem partB_weakExtComps_births (m N R : ℕ) (S : Finset Comp)
    (hS : ∀ v ∈ S, ∀ e ∈ v.births, m ≤ e.scale) :
    ∀ v ∈ weakExtComps m N R S, ∀ e ∈ v.births, m - 1 ≤ e.scale := by
  intro v hv e he
  unfold weakExtComps at hv
  rcases Finset.mem_union.1 hv with hv | hv
  · exact (Nat.sub_le m 1).trans (hS v hv e he)
  · obtain ⟨⟨u, t⟩, hut, rfl⟩ := Finset.mem_image.1 hv
    have hu := (Finset.mem_product.1 hut).1
    by_cases ht : t = []
    · simp only [succComp, ht, ↓reduceDIte] at he
      exact (Nat.sub_le m 1).trans (hS u hu e he)
    · simp only [succComp, ht, ↓reduceDIte, List.mem_cons] at he
      rcases he with rfl | he
      · exact le_rfl
      · exact (Nat.sub_le m 1).trans (hS u hu e he)

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

theorem partB_stage_invariant (c : WeakPassageInstance plan R) :
    ∀ n, n ≤ A.Jw →
      (c.stage (c.M + A.Jw - n)).level = c.M + A.Jw - n ∧
      (∀ v ∈ (c.stage (c.M + A.Jw - n)).comps, ∀ e ∈ v.births, c.M + A.Jw - n ≤ e.scale) ∧
      (c.stage (c.M + A.Jw - n)).comps.card ≤
        (1 + (wordsUpTo (weakAlphabet A.Nw) A.Rw).card) ^ n := by
  obtain ⟨-, hroot, hpass⟩ := c.construction
  intro n
  induction n with
  | zero =>
    intro _
    obtain ⟨hlev, hcomps, -⟩ := hroot
    simp only [Nat.sub_zero]
    refine ⟨hlev, ?_, ?_⟩
    · intro v hv e he
      rw [hcomps, Finset.mem_singleton] at hv
      rw [hv] at he
      simp at he
    · rw [hcomps]
      simp
  | succ n ih =>
    intro hn
    obtain ⟨hl, hb, hc⟩ := ih (by omega)
    have hi : c.M < c.M + A.Jw - n := by omega
    have hit : c.M + A.Jw - n ≤ c.M + A.Jw := Nat.sub_le _ _
    obtain ⟨⟨-, hlev', -, hcomps', -⟩, -⟩ := hpass _ hi hit
    have hidx : c.M + A.Jw - (n + 1) = c.M + A.Jw - n - 1 := by omega
    rw [hl] at hlev' hcomps'
    rw [hidx]
    refine ⟨by rw [hlev'], ?_, ?_⟩
    · rw [hcomps']
      exact partB_weakExtComps_births _ _ _ _ hb
    · rw [hcomps', pow_succ, mul_comm]
      exact (partB_weakExtComps_card _ _ _ _).trans
        (Nat.mul_le_mul_left _ hc)

theorem partB_wordsUpTo_mono (A : Finset WordLetter) (L : ℕ) :
    wordsUpTo A L ⊆ wordsUpTo A (L + 1) := by
  intro w hw
  simp only [wordsUpTo, Finset.mem_biUnion, Finset.mem_Icc] at hw ⊢
  obtain ⟨k, hk, hw⟩ := hw
  exact ⟨k, ⟨hk.1, by omega⟩, hw⟩

/-- **The count of the menu**: a bound for the number of components of a passage stage and for
the number of children of a component. -/
def weakReadoutCountConst {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ :=
  (1 + (wordsUpTo (weakAlphabet A.Nw) A.Rw).card) ^ A.Jw +
    ((wordsUpTo (weakAlphabet A.Nw) (A.Rw + 1)).card + 1)

/-- The counts of a passage stage at the named constant. -/
theorem weakReadoutCount_at (plan : WeakPassagePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) :
    Fintype.card (CompIn (c.stage i).comps) ≤ weakReadoutCountConst A ∧
      ∀ v : Comp, (Finset.univ.filter
        fun v' : CompIn (c.stage (i - 1)).comps => compParent i v'.1 = v).card ≤
          weakReadoutCountConst A := by
  classical
  unfold weakReadoutCountConst
  have hinv := partB_stage_invariant c (c.M + A.Jw - i) (by omega)
  have hidx : c.M + A.Jw - (c.M + A.Jw - i) = i := by omega
  rw [hidx] at hinv
  obtain ⟨hl, hb, hc⟩ := hinv
  refine ⟨?_, fun v => ?_⟩
  · calc Fintype.card (CompIn (c.stage i).comps) = (c.stage i).comps.card := Fintype.card_coe _
      _ ≤ (1 + (wordsUpTo (weakAlphabet A.Nw) A.Rw).card) ^ (c.M + A.Jw - i) := hc
      _ ≤ (1 + (wordsUpTo (weakAlphabet A.Nw) A.Rw).card) ^ A.Jw :=
          Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ _ := Nat.le_add_right _ _
  · obtain ⟨-, -, hpass⟩ := c.construction
    obtain ⟨⟨-, -, -, hcomps', -⟩, -⟩ := hpass i hi hit
    rw [hl] at hcomps'
    have hsub : (c.stage (i - 1)).comps ⊆
        succExtComps i (weakAlphabet A.Nw) A.Rw (c.stage i).comps := by
      rw [hcomps']
      unfold weakExtComps succExtComps
      exact Finset.union_subset_union le_rfl (Finset.image_subset_image
        (Finset.product_subset_product le_rfl (partB_wordsUpTo_mono _ _)))
    exact (Construction.Preservation.FullLift.readout_indexed_fiber_card_le (by omega) hb hsub
      v).trans (Nat.le_add_left _ _)

end AVRegularity.Providers.WeakGen.Residual
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual

/-! **Coarse readout energy, Part B: clause 1 at the family level**.

`weakCoarseFamilyRep`: `WeakCoarseFamilyRepStatement`. The classical representative `h.aU t v`
of the truncation `r.Ur (i-1) v t` (order `L_w`) of the high family is one of the high family to
every order `r` with `r + 2 ≤ K_w + m` (`partB_rep_lift`).
-/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction PartB

theorem weakCoarseFamilyRep (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ) :
    WeakCoarseFamilyRepStatement plan kOf := by
  intro B A R m _ hk c r Uhi i _ _ h hval v t ht
  have ha := h.representative v t ht
  rw [← hval v t ht] at ha
  have hK : R.Kw + m ≤ weakReductionReserve R m v.1 := Nat.le_add_right _ _
  exact partB_rep_lift (weakReductionReserve_kw_le R m v.1) (by omega) (Uhi (i - 1) v t)
    (h.aU t v) ha
end

/-! **Coarse readout energy, Part B: the mass bound**.

`weakReadoutMass`: `WeakReadoutMassStatement`. With `c' = succComp i p w` (`p` the parent, `w` the
word) one has `π_{c'} = π_p g`, `g = (c_w E^{η₀/2})^{|w|} ∈ (0,1]` (`weakMass_succComp`), and the
readout factor `ρ = (E^{η₀})^{|w|} ≤ 1`; hence `π_p⁻¹ ρ² ≤ π_p⁻¹ g⁻¹ = π_{c'}⁻¹`.
-/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction PartB

theorem weakReadoutMass (plan : WeakPassagePlan) : WeakReadoutMassStatement plan := by
  intro B A R c i c'
  have hΛ : 128 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (plan.base_ge B).trans c.base_ge
  have hq : 1 < c.D.q := by
    rw [c.q_eq]
    exact B.hq.1
  have hbasic := Scales.epsilon_basic (m := i - 1) hq hΛ
  have hE0 : 0 < c.D.eps (i - 1) := hbasic.1
  have hE1 : c.D.eps (i - 1) ≤ 1 := hbasic.2.1
  have hη : 0 < A.η₀ := A.η₀_pos
  have hρ0 : 0 ≤ (c.D.eps (i - 1) ^ A.η₀) ^ (compWord i c').length :=
    pow_nonneg (Real.rpow_nonneg hE0.le _) _
  have hρ1 : (c.D.eps (i - 1) ^ A.η₀) ^ (compWord i c').length ≤ 1 :=
    pow_le_one₀ (Real.rpow_nonneg hE0.le _) (Real.rpow_le_one hE0.le hE1 hη.le)
  refine ⟨?_, hρ1⟩
  have hmass := weakMass_succComp c.D A.Nw A.Jw i A.η₀ (compParent i c') (compWord i c')
  rw [Construction.Preservation.FullLift.succComp_parent_word i c'] at hmass
  have hcw0 : 0 < weakCw A.Nw A.Jw := by
    unfold weakCw
    have := A.Nw_pos
    have := A.Jw_pos
    positivity
  have hcw1 : weakCw A.Nw A.Jw ≤ 1 := by
    unfold weakCw
    refine inv_le_one_of_one_le₀ ?_
    have h1 : 1 ≤ A.Nw := A.Nw_pos
    have h2 : 1 ≤ A.Jw := A.Jw_pos
    have : 1 ≤ 4 * A.Nw * A.Jw := by nlinarith
    exact_mod_cast this
  have hbase0 : 0 < weakCw A.Nw A.Jw * c.D.eps (i - 1) ^ (A.η₀ / 2) :=
    mul_pos hcw0 (Real.rpow_pos_of_pos hE0 _)
  have hbase1 : weakCw A.Nw A.Jw * c.D.eps (i - 1) ^ (A.η₀ / 2) ≤ 1 :=
    (mul_le_mul hcw1 (Real.rpow_le_one hE0.le hE1 (by linarith)) (Real.rpow_nonneg hE0.le _)
      zero_le_one).trans_eq (one_mul 1)
  set g := (weakCw A.Nw A.Jw * c.D.eps (i - 1) ^ (A.η₀ / 2)) ^ (compWord i c').length with hg
  have hg0 : 0 < g := pow_pos hbase0 _
  have hg1 : g ≤ 1 := pow_le_one₀ hbase0.le hbase1
  have hsq : ((c.D.eps (i - 1) ^ A.η₀) ^ (compWord i c').length) ^ 2 ≤ 1 :=
    pow_le_one₀ hρ0 hρ1
  rw [hmass, mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (partB_mass_pos c _).le)
  have h1 : ((c.D.eps (i - 1) ^ A.η₀) ^ (compWord i c').length) ^ 2 * g ≤ 1 :=
    (mul_le_mul hsq hg1 hg0.le zero_le_one).trans_eq (one_mul 1)
  calc ((c.D.eps (i - 1) ^ A.η₀) ^ (compWord i c').length) ^ 2
      = ((c.D.eps (i - 1) ^ A.η₀) ^ (compWord i c').length) ^ 2 * g * g⁻¹ := by
        field_simp
    _ ≤ 1 * g⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hg0.le)
    _ = g⁻¹ := one_mul _
end

end AVRegularity.Providers.WeakGen.Residual
end

section
namespace AVRegularity.Providers.WeakGen.Residual

/-! **The frontier masses**: positivity, the old components, the
frontier components (`weakFrontierMass_inv_frontier`), the children `succComp i x w`, and the
real-number identities behind them. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction PartB

/-- Abstract power identity of the frontier masses. -/
theorem frontier_mass_inv_pow {π E X : ℝ} (n : ℕ) :
    (π * (((E ^ 2)⁻¹) * X) ^ n)⁻¹ = π⁻¹ * (E ^ n) ^ 2 * (X ^ n)⁻¹ := by
  rw [mul_pow, inv_pow, mul_inv, mul_inv, inv_inv, ← pow_mul, ← pow_mul, mul_comm n 2]
  ring

/-- The exponent identity `(x^{4a})^n = x^{4an}`. -/
theorem frontier_rpow_pow {x : ℝ} (hx : 0 < x) (a : ℝ) (n : ℕ) :
    (x ^ (4 * a)) ^ n = x ^ (4 * a * n) := by
  rw [Real.rpow_mul_natCast hx.le]

/-- The real arithmetic of an eddy edge at the frontier masses. -/
theorem frontier_eddy_real {E x p Cw a η : ℝ} (hE : 0 < E) (hx : 0 < x) (hEx : E ≤ x)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hb : p ≤ Cw * E ^ a) :
    Real.sqrt ((((E ^ η) ^ 2)⁻¹ * x ^ (4 * a))⁻¹) * (E ^ (-η) * p ^ 2) ≤ Cw ^ 2 := by
  have hu : 0 < E ^ η := Real.rpow_pos_of_pos hE _
  have hy : 0 < x ^ (2 * a) := Real.rpow_pos_of_pos hx _
  have h4 : x ^ (4 * a) = (x ^ (2 * a)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; congr 1; push_cast; ring
  have hs : Real.sqrt ((((E ^ η) ^ 2)⁻¹ * x ^ (4 * a))⁻¹) = E ^ η / x ^ (2 * a) := by
    rw [h4, show (((E ^ η) ^ 2)⁻¹ * (x ^ (2 * a)) ^ 2)⁻¹ = (E ^ η / x ^ (2 * a)) ^ 2 by
      field_simp]
    exact Real.sqrt_sq (div_nonneg hu.le hy.le)
  rw [hs, Real.rpow_neg hE.le]
  have hp2 : p ^ 2 ≤ Cw ^ 2 * E ^ (2 * a) := by
    have := pow_le_pow_left₀ hp hb 2
    rw [mul_pow, ← Real.rpow_natCast (E ^ a) 2, ← Real.rpow_mul hE.le] at this
    simpa [mul_comm] using this
  have hEy : E ^ (2 * a) ≤ x ^ (2 * a) := Real.rpow_le_rpow hE.le hEx (by linarith)
  calc E ^ η / x ^ (2 * a) * ((E ^ η)⁻¹ * p ^ 2) = p ^ 2 / x ^ (2 * a) := by
        field_simp
    _ ≤ Cw ^ 2 * E ^ (2 * a) / x ^ (2 * a) := by gcongr
    _ ≤ Cw ^ 2 * x ^ (2 * a) / x ^ (2 * a) := by gcongr
    _ = Cw ^ 2 := by field_simp

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

theorem frontier_eps_pos (c : WeakPassageInstance plan R) (j : ℕ) : 0 < c.D.eps j := by
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge B).trans c.base_ge)
  exact Construction.Stream.ocEpsilon_pos hΛ

theorem weakFrontierLetter_pos (c : WeakPassageInstance plan R) (i : ℕ) :
    0 < weakFrontierLetter c i := by
  unfold weakFrontierLetter
  have := frontier_eps_pos c (i - 1)
  have := frontier_eps_pos c c.M
  positivity

/-- the frontier masses are positive. -/
theorem weakFrontierMass_pos (c : WeakPassageInstance plan R) (i : ℕ) (v : Comp) :
    0 < weakFrontierMass c i v := by
  unfold weakFrontierMass
  exact mul_pos (partB_mass_pos c _) (pow_pos (weakFrontierLetter_pos c i) _)

theorem compParent_eq_of_compWord_nil (i : ℕ) (c : Comp) (h : compWord i c = []) :
    compParent i c = c := by
  rcases c with ⟨r, bs⟩
  cases bs with
  | nil => simp [compParent]
  | cons e rest =>
    by_cases he : e.scale = i - 1
    · exact absurd (by simpa [compWord, he] using h) e.word_ne_nil
    · simp [compParent, he]

/-- on a component with empty word the frontier mass is the weak mass. -/
theorem weakFrontierMass_of_word_nil (c : WeakPassageInstance plan R) (i : ℕ) (v : Comp)
    (h : compWord i v = []) :
    weakFrontierMass c i v = weakMass c.D A.Nw A.Jw A.η₀ v := by
  unfold weakFrontierMass
  rw [h, compParent_eq_of_compWord_nil i v h]
  simp

/-- the inverse frontier mass on the frontier. -/
theorem weakFrontierMass_inv_frontier (c : WeakPassageInstance plan R) (i : ℕ) (v : Comp)
    (h : (compWord i v).length = A.Rw) :
    (weakFrontierMass c i v)⁻¹ =
      (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v))⁻¹ *
        ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2 *
        (c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw))⁻¹ := by
  have hx := frontier_eps_pos c c.M
  unfold weakFrontierMass weakFrontierLetter
  rw [h, frontier_mass_inv_pow A.Rw, frontier_rpow_pow hx]

/-- The frontier mass of a child `(x, w)`, for `x` among the old components of the passage. -/
theorem weakFrontierMass_succComp (c : WeakPassageInstance plan R) (i : ℕ) (hi : 1 ≤ i)
    (x : Comp) (hx : ∀ e ∈ x.births, i ≤ e.scale) (w : List WordLetter) :
    weakFrontierMass c i (succComp i x w) =
      weakMass c.D A.Nw A.Jw A.η₀ x * weakFrontierLetter c i ^ w.length := by
  obtain ⟨h1, h2⟩ := Construction.Preservation.FullLift.parent_word_succComp hi x hx w
  unfold weakFrontierMass
  rw [h1, h2]
end

/-! **The stored total at the frontier masses is bounded**.

`weakFrontierStoredTotal_le`: the bound, under the floors of the coarse energy
(`WeakCoarseFloorsOK plan`). The constant is the named function
`weakFrontierStoredConst`, a function of the request only. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction PartB

/-- The constant of the Péclet bound `Pe_i ≤ C_w ε_{i-1}^{a_*}` of the base. -/
def weakFrontierEddyConst (B : WeakCoefficientBase) : ℝ :=
  (EntryScales.weak_scales_core B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq).choose

/-- **The constant `T₀` of the stored total at the frontier masses**: `Q (1 + C_w²)`, `Q` the
passage budget of the menu, and at least one. -/
def weakFrontierStoredConst {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (_R : WeakPassageRequest A) : ℝ :=
  max 1 ((weakStoredPassageBudget A.Nw A.Jw A.Rw : ℝ) * (1 + weakFrontierEddyConst B ^ 2))

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The stored total of the stage `i - 1` at the frontier masses is at most `T₀`. -/
theorem weakFrontierStoredTotal_le (hfl : WeakCoarseFloorsOK plan) (c : WeakPassageInstance plan R)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) :
    weakFrontierStoredTotal c i ≤ weakFrontierStoredConst R := by
  classical
  have h128 : 128 ≤ A.Λ := (plan.base_ge B).trans c.base_ge
  have hq := c.construction
  have hlev := EntryWeakProofs.weakConstruction_level c.P _ c.M A.Jw 0 _ c.stage hq i hi.le hit
  have ht := EntryWeakProofs.weakConstruction_stage_hasTags c.P _ c.M A.Jw 0 _ hq i hi.le hit
  have hp := hq.2.2 i hi hit
  have hpath := EntryWeakProofs.weakConstruction_path_length_bound c.P _ c.M A.Jw 0 _ c.stage hq
    i hi.le hit
  have hcomp := weakConstruction_card_le c.P _ c.M A.Jw 0 _ c.stage hq i hi.le hit
  have hsmall : weakStoredTotal (c.stage i) A.Nw A.Jw A.η₀ ≤ 1 :=
    weakRaw_storedTotal_le (weakPassageRawSetting c)
      ((hfl.2 R c.j₀).2.2.1.trans c.level_ge) i hi.le hit
  have hold := (partB_stage_invariant c (c.M + A.Jw - i) (by omega))
  have hidx : c.M + A.Jw - (c.M + A.Jw - i) = i := by omega
  rw [hidx] at hold
  obtain ⟨-, hbirth, -⟩ := hold
  have hi1 : 1 ≤ i := by omega
  have heps := frontier_eps_pos c
  -- the Péclet bound
  have hPe : c.D.weakPe i ≤ weakFrontierEddyConst B * c.D.eps (i - 1) ^ weakAStar B.α B.q := by
    have hh := (EntryScales.weak_scales_core B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq).choose_spec.2
      A.Λ h128 c.M (c.D.κ c.M) c.band.1 i hi
    simpa only [OCData.weakPe, OCData.kap, c.terminal, min_eq_right hi.le, OCData.eps, c.alpha,
      c.q_eq, c.base_eq, weakAStar, weakFrontierEddyConst] using hh.1
  have hPe0 : 0 ≤ c.D.weakPe i := by
    have hν : 0 < c.D.κ c.M := CycleReference.bandChain_pos (by omega) B.hζ c.band le_rfl
    unfold OCData.weakPe OCData.kap
    rw [c.terminal, min_eq_right hi.le]
    exact div_nonneg (Real.rpow_nonneg (heps i).le _) hν.le
  have hEx : c.D.eps (i - 1) ≤ c.D.eps c.M := by
    simpa only [OCData.eps, c.q_eq, c.base_eq] using
      EntryScales.epsilon_antitone B.hq.1 h128 (by omega : c.M ≤ i - 1)
  have hastar : 0 ≤ weakAStar B.α B.q := by
    unfold weakAStar
    exact mul_nonneg (by linarith [B.hq.1])
      (Scales.admissible_exponent_facts B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq).1.le
  have hC0 : 0 ≤ weakFrontierEddyConst B ^ 2 := sq_nonneg _
  have hmain := weakFrontier_total_uniform (weakFrontierMass c i) (weakFrontierEddyConst B ^ 2)
    hC0 c.P _ A.Jw (1 + (c.M + A.Jw - i) * A.Nw) _ (c.stage i) (c.stage (i - 1)) hp.1 ht hp.2
    A.Nw_pos A.Jw_pos heps hpath hsmall hcomp
    (by apply Nat.add_le_add_left; exact Nat.mul_le_mul_right _ (by omega)) ?_ ?_
  · refine hmain.trans ?_
    unfold weakFrontierStoredConst
    refine le_trans (le_of_eq ?_) (le_max_right _ _)
    rfl
  · intro w h π
    rw [hlev]
    have hsrc : π.src = (π.step 0).2.1.1 := by simp [StagePath.src]
    have htgt : π.tgt = (π.step (Fin.last h)).1.1 := by simp [StagePath.tgt, Fin.last]
    have hs : ∀ e ∈ π.src.births, i ≤ e.scale := hbirth _ (by rw [hsrc]; exact (π.step 0).2.1.2)
    have ht' : ∀ e ∈ π.tgt.births, i ≤ e.scale :=
      hbirth _ (by rw [htgt]; exact (π.step (Fin.last h)).1.2)
    rw [weakFrontierMass_succComp c i hi1 _ hs, weakFrontierMass_succComp c i hi1 _ ht',
      weakMass_succComp, weakMass_succComp]
    have hg : 0 < weakCw A.Nw A.Jw * c.D.eps (i - 1) ^ (A.η₀ / 2) :=
      mul_pos (weakCw_strict_pos A.Nw A.Jw A.Nw_pos A.Jw_pos)
        (Real.rpow_pos_of_pos (heps _) _)
    rw [mul_div_mul_right _ _ (pow_pos (weakFrontierLetter_pos c i) _).ne',
      mul_div_mul_right _ _ (pow_pos hg _).ne']
  · intro v w n
    rw [hlev]
    have hv := hbirth _ v.2
    rw [weakFrontierMass_succComp c i hi1 _ hv, weakFrontierMass_succComp c i hi1 _ hv,
      List.length_append, List.length_singleton, pow_succ]
    have hθ := weakFrontierLetter_pos c i
    have hm := partB_mass_pos c v.1
    rw [show weakMass c.D A.Nw A.Jw A.η₀ v.1 * weakFrontierLetter c i ^ w.length /
        (weakMass c.D A.Nw A.Jw A.η₀ v.1 * (weakFrontierLetter c i ^ w.length *
          weakFrontierLetter c i)) = (weakFrontierLetter c i)⁻¹ by field_simp]
    exact frontier_eddy_real (frontier_eps_pos c _) (frontier_eps_pos c c.M) hEx hastar hPe0 hPe
end

end AVRegularity.Providers.WeakGen.Residual
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! **The raw frontier estimate**.

`weakCoarseRawFrontier_named`: the raw frontier bound (`WeakCoarseRawFrontierAt`) with the NAMED
constant `weakCoarseFrontierConst (plan.radius R) R m`, a function of the radius and the request.
The proof is that of the high-reserve energy: the passage energy at the frontier masses
`μ_v = weakFrontierMass c i v` (`weakFrontier_raw_energy`, stored total
`weakFrontierStoredConst R`), the frontier terms are at most `x^{4a_*R_w}` times the `μ`-weighted
energy, and the datum, which vanishes on the new components and has `μ = π` on the old ones, is
bounded by the trace bound of the high-reserve energy statement. -/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction PartB

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The constant of the raw frontier estimate**: `C_gen(T₀, ρ, R) · c_Q²`, `T₀` the stored total, `c_Q` the
trace constant of the high-reserve energy statement. -/
def weakCoarseFrontierConst (ρ : ℝ) (R : WeakPassageRequest A) (m : ℕ) : ℝ :=
  weakFrontierPassageConst (weakFrontierStoredConst R) ρ R *
    (max 1 ((weakQuietCoefficientPlan weakCoarseQuietSeed).traceC
      (weakEntryLiftRequest R m))) ^ 2

theorem weakFrontierPassageConst_nonneg (T₀ ρ : ℝ) (R : WeakPassageRequest A) :
    0 ≤ weakFrontierPassageConst T₀ ρ R := by
  unfold weakFrontierPassageConst
  exact mul_nonneg zero_le_two (Finset.sum_nonneg fun n _ => pow_nonneg (by positivity) n)

theorem weakCoarseFrontierConst_nonneg (ρ : ℝ) (R : WeakPassageRequest A) (m : ℕ) :
    0 ≤ weakCoarseFrontierConst ρ R m :=
  mul_nonneg (weakFrontierPassageConst_nonneg _ _ _) (sq_nonneg _)

/-- The frontier term of the statement is at most `x^{4a_*R_w}` times the `μ`-weighted term. -/
theorem frontier_term_le (c : WeakPassageInstance plan R) (i : ℕ) (v : Comp) (F : ℝ)
    (hF : 0 ≤ F) :
    (if (compWord i v).length = A.Rw then
      (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v))⁻¹ *
        ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2 * F else 0) ≤
      c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw) * ((weakFrontierMass c i v)⁻¹ * F) := by
  have hX : 0 < c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw) :=
    Real.rpow_pos_of_pos (frontier_eps_pos c _) _
  have hμ := weakFrontierMass_pos c i v
  split_ifs with h
  · rw [weakFrontierMass_inv_frontier c i v h]
    refine le_of_eq ?_
    field_simp
  · exact mul_nonneg hX.le (mul_nonneg (inv_nonneg.2 hμ.le) hF)

theorem frontier_term_nonneg (c : WeakPassageInstance plan R) (i : ℕ) (v : Comp) (F : ℝ)
    (hF : 0 ≤ F) :
    0 ≤ (if (compWord i v).length = A.Rw then
      (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v))⁻¹ *
        ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2 * F else 0) := by
  split_ifs
  · exact mul_nonneg (mul_nonneg (inv_nonneg.2 (partB_mass_pos c _).le) (sq_nonneg _)) hF
  · exact le_rfl

/-- A component of the stage `i` has empty word at the passage `i`. -/
theorem compWord_nil_of_old (i : ℕ) (hi : 1 ≤ i) (v : Comp)
    (hv : ∀ e ∈ v.births, i ≤ e.scale) : compWord i v = [] := by
  rcases v with ⟨r, bs⟩
  cases bs with
  | nil => simp [compWord]
  | cons e rest =>
    have : e.scale ≠ i - 1 := by
      have := hv e (by simp)
      omega
    simp [compWord, this]

/-- **The raw frontier estimate with the named constant**, with every hypothesis as an argument. The hypothesis `hvr`
(the top-level family is the run's on `[t_{M+J_w+1}, a + T₀]`) is a clause of
`WeakCoarseRawFrontierAt`. -/
theorem weakCoarseRawFrontier_named (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarsePlanOK plan) (m : ℕ) (hm : m ≤ weakEntryMmax R)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (hstart : r.a < r.tq (c.M + A.Jw + 1))
    (Uhi : ∀ i, WeakStageFamily (weakPassageRawSetting c) m i)
    (Whi : ∀ i, WeakStageLift (weakPassageRawSetting c) m i)
    (hpass : ∀ i, c.M < i → i ≤ c.M + A.Jw →
      WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi i)
    (hvr : ∀ v : CompIn (c.stage (c.M + A.Jw)).comps,
        ∀ t ∈ Set.Icc (r.tq (c.M + A.Jw + 1)) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (c.M + A.Jw) v t) =
          r.Ur (c.M + A.Jw) v t)
    (hval : ∀ i, c.M < i → i ≤ c.M + A.Jw → ∀ v : CompIn (c.stage (i - 1)).comps,
        ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
          r.Ur (i - 1) v t)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (Φ : ℝ)
    (hΦ : ∀ t ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀),
      weightedNorm 1 (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1)
        (fun v => truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t)) ≤ Φ)
    (t : ℝ) (ht : t ∈ Set.Icc (r.tq i) (r.a + A.T₀)) :
    ENNReal.ofReal (∑ v : CompIn (c.stage (i - 1)).comps,
          if (compWord i v.1).length = A.Rw then
            (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v.1))⁻¹ *
              ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2 *
              factorialNormSq (plan.radius R * c.D.eps (i - 1)) (Uhi (i - 1) v t).val
          else 0) +
        ENNReal.ofReal (c.D.κ c.M / 2) *
          ∫⁻ τ in Set.Icc (r.tq i) (r.a + A.T₀),
            ENNReal.ofReal (∑ v : CompIn (c.stage (i - 1)).comps,
              if (compWord i v.1).length = A.Rw then
                (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v.1))⁻¹ *
                  ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2 *
                  gradFactorialNormSq (plan.radius R * c.D.eps (i - 1)) (Whi (i - 1) v τ).val
              else 0) ≤
      ENNReal.ofReal (weakCoarseFrontierConst (plan.radius R) R m *
        c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw) * Φ ^ 2) := by
  classical
  have hok' := hok
  obtain ⟨hfl, hfit⟩ := hok
  obtain ⟨hrad2048, hfl2⟩ := hfl
  obtain ⟨hcf, hdf, hsf, hpf⟩ := hfl2 R c.j₀
  have hlevel := c.level_ge
  have hL : c.M ≤ i - 1 := by omega
  have hLJ : i - 1 < c.M + A.Jw := by omega
  have hi1 : 1 ≤ i := by omega
  have hlev : ((weakPassageRawSetting c).stage (i - 1)).level = i - 1 :=
    (weakPassageRawSetting c).level_eq (i - 1) hL hLJ.le
  have hkap : (weakPassageRawSetting c).D.kap ((weakPassageRawSetting c).stage (i - 1)).level =
      (weakPassageRawSetting c).D.κ (weakPassageRawSetting c).M := by
    rw [hlev]; exact (weakPassageRawSetting c).kap_eq _ hL
  have hs := hpass i hi hit
  unfold WeakStagePassage at hs
  rw [hkap, hlev] at hs
  have hT := weakFrontierStoredTotal_le ⟨hrad2048, fun R' j => hfl2 R' j⟩ c i hi hit
  have hμ : ∀ v : CompIn (c.stage (i - 1)).comps, 0 < weakFrontierMass c i v.1 :=
    fun v => weakFrontierMass_pos c i v.1
  have hreal := weakFrontier_raw_energy (weakPassageRawSetting c)
    (weakPassage_coeffRegular hcommon c) (hcf.trans hlevel) (hsf.trans hlevel) (plan.radius R)
    (plan.radius_pos R) ((hrad2048 R).trans (by norm_num)) (r.tq i) (r.a + A.T₀)
    (fun L hL' => weakCoarse_passage_drift ⟨hrad2048, fun R' j => hfl2 R' j⟩ c
      (by have := weakPassage_two_le_M hcommon c; omega) L hL' _ _ _) m hm Uhi Whi i hi hit
    ((weakPassageRawClock r).tq_le i hi hit) hs (weakFrontierStoredConst R)
    (fun v => weakFrontierMass c i v.1) hμ hT t ht
  have hX : 0 ≤ c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw) :=
    (Real.rpow_pos_of_pos (frontier_eps_pos c _) _).le
  have hκ : 0 ≤ c.D.κ c.M / 2 := by
    have := (weakPassageRawSetting c).kappa_pos
    exact div_nonneg this.le zero_le_two
  have hgi : ∀ v : CompIn (c.stage (i - 1)).comps,
      Integrable (fun τ => gradFactorialNormSq (plan.radius R * c.D.eps (i - 1))
        (Whi (i - 1) v τ).val) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))) := fun v =>
    CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hs.2.1 v)
  have hGint : Integrable (fun τ => ∑ v : CompIn (c.stage (i - 1)).comps,
      if (compWord i v.1).length = A.Rw then
        (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v.1))⁻¹ *
          ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2 *
          gradFactorialNormSq (plan.radius R * c.D.eps (i - 1)) (Whi (i - 1) v τ).val
      else 0) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))) := by
    refine integrable_finsetSum _ fun v _ => ?_
    by_cases h : (compWord i v.1).length = A.Rw
    · simp only [h, ite_true]
      exact (hgi v).const_mul _
    · simp only [h, ite_false]
      exact integrable_zero _ _ _
  have hGint' : Integrable (fun τ => ∑ v : CompIn (c.stage (i - 1)).comps,
      (weakFrontierMass c i v.1)⁻¹ *
        gradFactorialNormSq (plan.radius R * c.D.eps (i - 1)) (Whi (i - 1) v τ).val)
      (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))) :=
    integrable_finsetSum _ fun v _ => (hgi v).const_mul _
  have hSF : (∑ v : CompIn (c.stage (i - 1)).comps,
      if (compWord i v.1).length = A.Rw then
        (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v.1))⁻¹ *
          ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2 *
          factorialNormSq (plan.radius R * c.D.eps (i - 1)) (Uhi (i - 1) v t).val
      else 0) ≤ c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw) *
        ∑ v : CompIn (c.stage (i - 1)).comps, (weakFrontierMass c i v.1)⁻¹ *
          factorialNormSq (plan.radius R * c.D.eps (i - 1)) (Uhi (i - 1) v t).val := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ =>
      frontier_term_le c i v.1 _ (factorialNormSq_nonneg _ _)
  have hGF : ∀ τ, (∑ v : CompIn (c.stage (i - 1)).comps,
      if (compWord i v.1).length = A.Rw then
        (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v.1))⁻¹ *
          ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2 *
          gradFactorialNormSq (plan.radius R * c.D.eps (i - 1)) (Whi (i - 1) v τ).val
      else 0) ≤ c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw) *
        ∑ v : CompIn (c.stage (i - 1)).comps, (weakFrontierMass c i v.1)⁻¹ *
          gradFactorialNormSq (plan.radius R * c.D.eps (i - 1)) (Whi (i - 1) v τ).val := by
    intro τ
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ =>
      frontier_term_le c i v.1 _ (CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _)
  have hint : (∫ τ in Set.Icc (r.tq i) (r.a + A.T₀), ∑ v : CompIn (c.stage (i - 1)).comps,
      if (compWord i v.1).length = A.Rw then
        (weakMass c.D A.Nw A.Jw A.η₀ (compParent i v.1))⁻¹ *
          ((c.D.eps (i - 1) ^ A.η₀) ^ A.Rw) ^ 2 *
          gradFactorialNormSq (plan.radius R * c.D.eps (i - 1)) (Whi (i - 1) v τ).val
      else 0) ≤ c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw) *
        ∫ τ in Set.Icc (r.tq i) (r.a + A.T₀), ∑ v : CompIn (c.stage (i - 1)).comps,
          (weakFrontierMass c i v.1)⁻¹ *
            gradFactorialNormSq (plan.radius R * c.D.eps (i - 1)) (Whi (i - 1) v τ).val := by
    rw [← integral_const_mul]
    exact integral_mono hGint (hGint'.const_mul _) hGF
  -- the datum
  have hdatum : ∑ v : CompIn (c.stage (i - 1)).comps, (weakFrontierMass c i v.1)⁻¹ *
      factorialNormSq (plan.radius R * c.D.eps (i - 1))
        (weakStageTrace (weakPassageRawSetting c) m i (Uhi i) (r.tq i) v).val =
      massNormSq (plan.radius R * c.D.eps (i - 1))
        (fun v : CompIn (c.stage (i - 1)).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (fun v => (weakStageTrace (weakPassageRawSetting c) m i (Uhi i) (r.tq i) v).val) := by
    unfold massNormSq
    refine Finset.sum_congr rfl fun v _ => ?_
    beta_reduce
    by_cases hv : v.1 ∈ (c.stage i).comps
    · have hinv := partB_stage_invariant c (c.M + A.Jw - i) (by omega)
      have hidx : c.M + A.Jw - (c.M + A.Jw - i) = i := by omega
      rw [hidx] at hinv
      have hw := compWord_nil_of_old i hi1 v.1 (hinv.2.1 _ hv)
      rw [weakFrontierMass_of_word_nil c i v.1 hw]
    · rw [weakStageTrace_new (weakPassageRawSetting c) m i (Uhi i) (r.tq i) v hv]
      simp [factorialNormSq, derivativeNormSq]
  have htr := weakCoarse_trace_bound hcommon m (hfit R m hm) c r hstart Uhi hvr hval i hi hit Φ hΦ
  have htr' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 htr
  refine ofReal_energy_le hκ hGint (fun τ => Finset.sum_nonneg fun v _ =>
    frontier_term_nonneg c i v.1 _ (CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _))
    (Finset.sum_nonneg fun v _ =>
      frontier_term_nonneg c i v.1 _ (factorialNormSq_nonneg _ _)) ?_
  have hC0 := weakFrontierPassageConst_nonneg (weakFrontierStoredConst R) (plan.radius R) R
  calc _ ≤ c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw) *
        (∑ v : CompIn (c.stage (i - 1)).comps, (weakFrontierMass c i v.1)⁻¹ *
          factorialNormSq (plan.radius R * c.D.eps (i - 1)) (Uhi (i - 1) v t).val +
        c.D.κ c.M / 2 * ∫ τ in Set.Icc (r.tq i) (r.a + A.T₀),
          ∑ v : CompIn (c.stage (i - 1)).comps, (weakFrontierMass c i v.1)⁻¹ *
            gradFactorialNormSq (plan.radius R * c.D.eps (i - 1)) (Whi (i - 1) v τ).val) := by
        have := add_le_add hSF (mul_le_mul_of_nonneg_left hint hκ)
        linarith only [this]
    _ ≤ c.D.eps c.M ^ (4 * weakAStar B.α B.q * A.Rw) *
        (weakFrontierPassageConst (weakFrontierStoredConst R) (plan.radius R) R *
          ((max 1 ((weakQuietCoefficientPlan weakCoarseQuietSeed).traceC
            (weakEntryLiftRequest R m))) ^ 2 * Φ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (hreal.trans ?_) hX
        rw [hdatum]
        exact mul_le_mul_of_nonneg_left htr' hC0
    _ = _ := by unfold weakCoarseFrontierConst; ring

/-- **The raw frontier estimate at the named constant** `weakCoarseFrontierConst (plan.radius R) R m`. -/
theorem weakCoarseRawFrontier_at (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarsePlanOK plan) (R : WeakPassageRequest A) (m : ℕ) (hm : m ≤ weakEntryMmax R) :
    WeakCoarseRawFrontierAt plan R m (weakCoarseFrontierConst (plan.radius R) R m) :=
  fun c r hstart Uhi Whi hpass hvr hval i hi hit Φ hΦ t ht =>
    weakCoarseRawFrontier_named hcommon hok m hm c r hstart Uhi Whi hpass hvr hval i hi hit Φ hΦ
      t ht

end AVRegularity.Providers.WeakGen.Residual
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! **The coarse readout energy, proved, at a named constant**.

With the raw frontier estimate proved, the readout energy has no analytic hypothesis:
`weakCoarseReadoutEnergy : WeakCoarseReadoutEnergyStatement plan kOf` under the plan conditions
`WeakPassageCommonOK plan` and `WeakCoarseReadoutPlanOK plan kOf`.

Its constant is named before the plan: `weakCoarseReadoutConst ρ R`, a function of the radius
`ρ = plan.radius R` and the request, built from the passage constant, the trace constant of the
fixed quiet seed, the stored total at the frontier masses and the counts of the menu. No floor of
the plan enters it, so the level floor of the common plan can be chosen after it
(`WeakGluingPricePlanOK plan prices Cen` with `Cen R := weakCoarseReadoutConst (plan.radius R) R`).

* `weakCoarseReadoutEnergy_named`: the body of (iv) at that constant.
* `WeakCoarseFrontierEnergyAt`, `weakCoarseFrontierEnergyAt_named`: the second bound (the
  length-`R_w` readout, with the gain `x^{2a_*R_w}`), in the form the response frontier
  consumes.

The degenerate cases are included: `R_w = 0` makes the frontier readout the readout of the old
components and the gain `1`; `Φ = 0` gives zero energies. The constant does not read `D_m`, the
level or the datum. -/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

/-- **The constant of (iv)**, a function of the radius and the request. -/
def weakCoarseReadoutConst {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (ρ : ℝ)
    (R : WeakPassageRequest A) : ℝ :=
  Real.sqrt (2 * (weakReadoutCountConst A : ℝ) * weakReadoutCountConst A *
      weakCoarseHighConst ρ R (weakEntryMmax R)) +
    Real.sqrt (2 * (weakReadoutCountConst A : ℝ) * weakReadoutCountConst A *
      weakCoarseFrontierConst ρ R (weakEntryMmax R))

theorem weakCoarseReadoutConst_nonneg {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (ρ : ℝ) (R : WeakPassageRequest A) : 0 ≤ weakCoarseReadoutConst ρ R :=
  add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

variable {plan : WeakPassagePlan}
  {kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ}

/-- **The body of (iv) at the named constant.** -/
theorem weakCoarseReadoutEnergy_named (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarseReadoutPlanOK plan kOf) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) :
    WeakCoarseReadoutEnergyBody plan kOf R (weakCoarseReadoutConst (plan.radius R) R) :=
  weakCoarseReadoutEnergy_core hok weakReadoutCS (weakReadoutMass plan)
    (weakCoarseFamilyRep plan kOf) R _ _ (weakReadoutCountConst A)
    (weakCoarseHighConst_nonneg _ R _) (weakCoarseFrontierConst_nonneg _ R _)
    (weakCoarse_high_energy_at hcommon hok.1 R (weakEntryMmax R) le_rfl)
    (weakCoarseRawFrontier_at hcommon hok.1 R (weakEntryMmax R) le_rfl)
    (fun c i hi hit => weakReadoutCount_at plan R c i hi hit)

/-- **(iv), the coarse readout energy**, with no analytic hypothesis. -/
theorem weakCoarseReadoutEnergy (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarseReadoutPlanOK plan kOf) : WeakCoarseReadoutEnergyStatement plan kOf :=
  fun R _ _ => ⟨_, weakCoarseReadoutConst_nonneg (plan.radius R) R,
    weakCoarseReadoutEnergy_named hcommon hok R⟩

/-- **The energy of the length-`R_w` readout at an explicit constant** `Cen`: the second bound of
(iv), with the gain `x^{2a_*R_w}`. -/
def WeakCoarseFrontierEnergyAt (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ)
    (Cen : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℝ) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A},
    A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1) →
    A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 < 2 * weakAStar B.α B.q * (A.Rw + 1) →
  ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → ∀ h : WeakComparisonInput r i,
    classicalStrongEnergy (plan.radius R * c.D.eps (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (Set.Icc (r.tq i) (r.a + A.T₀)) (kOf R)
        (fun t x v => weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v x) ≤
      ENNReal.ofReal (Cen R * c.D.eps c.M ^ (2 * weakAStar B.α B.q * A.Rw) * h.Φ)

/-- The second bound of (iv) at the named constant. -/
theorem weakCoarseFrontierEnergyAt_named (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarseReadoutPlanOK plan kOf) :
    WeakCoarseFrontierEnergyAt plan kOf (fun R => weakCoarseReadoutConst (plan.radius R) R) :=
  fun {_B} {_A} {R} _ _ c r i hi hit h =>
    (weakCoarseReadoutEnergy_named hcommon hok R c r i hi hit h).2.2.2

end AVRegularity.Providers.WeakGen.Residual
end
end
