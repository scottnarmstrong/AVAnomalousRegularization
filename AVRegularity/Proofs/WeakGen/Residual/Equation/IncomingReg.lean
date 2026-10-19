-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.Equation.IncomingPassage
import AVRegularity.Proofs.WeakGen.Reduction.ScalarIdentification
public import AVRegularity.EntryWeakAssembly.QuietScalarEvolution

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Residual

/-! **The equation of the incoming family, the root case `i = M + J_w`**. The root stage has the single component
`⟨0, []⟩` and no edges; `r.Ur (M + J_w)` is constrained by `r.reduction` only through its value
(equal to `θ`), and `r.Urw (M + J_w)` is free, so the `H¹` lift is produced here from the scalar
solution (`weak_identification_core`). -/

open WeakEntryProofs WeakEntryProofs.Assembly

/-- Transport of a weak identity along equal carriers and equal total fluxes. -/
theorem coupledWeakIdentity_data_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {k : ℕ}
    {μ : Measure (Vec 2)} {ν a t : ℝ} {v : ℝ → Vec 2 → Vec 2} {u u' f f' : TorusHk k E}
    {φ : Vec 2 → E} {dφ : Fin 2 → Vec 2 → E} {du : ℝ → Fin 2 → Vec 2 → E}
    {A A' F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} {g : ℝ → Vec 2 → E}
    (hu : u = u') (hf : f = f') (hA : A = A')
    (h : CoupledWeakIdentity μ ν a t v (u'.toFunction.jet (valueIndex2 k))
      (f'.toFunction.jet (valueIndex2 k)) φ dφ du A F g) :
    CoupledWeakIdentity μ ν a t v (u.toFunction.jet (valueIndex2 k))
      (f.toFunction.jet (valueIndex2 k)) φ dφ du A' F g := by
  subst hu hf hA; exact h

private theorem truncate_valueIndex_root {m n : ℕ} (hmn : m ≤ n) :
    truncateJetIndex hmn (valueIndex2 m) = valueIndex2 n := by
  apply Sigma.ext
  · apply Fin.ext
    rfl
  · simp [truncateJetIndex, valueIndex2, valueIndex]

/-- At the root level the incoming family has the value of the scalar solution. -/
theorem weakIncoming_root_scalar {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) :
    ∃ (u' : ℝ → TorusHk 0 ℝ) (w' : ℝ → TorusHk (0 + 1) ℝ),
      WeakScalarTorusSolution (c.D.κ c.M) (r.tq (c.M + A.Jw)) (r.a + A.T₀)
        (streamVel (c.D.Φ (c.M + A.Jw))) 0 (u' (r.tq (c.M + A.Jw))) u' w' ∧
      ∀ (v : CompIn (c.stage (c.M + A.Jw)).comps), ∀ t ∈ Set.Icc (r.tq (c.M + A.Jw)) (r.a + A.T₀),
        weakIncomingVal r (c.M + A.Jw) v t = u' t := by
  have hJ : (c.M < c.M + A.Jw) := by have := A.Jw_pos; omega
  have h128 : 128 ≤ A.Λ := (plan.base_ge B).trans c.base_ge
  have hΛ : 1 ≤ c.D.Λ := by rw [c.base_eq]; omega
  have hb : Applications.IsContDrift (streamVel (c.D.Φ (c.M + A.Jw))) :=
    Reduction.streamSeq_isContDrift B.hζ h128 c.streams (c.M + A.Jw)
  have hstep := (r.reduction.2.2.2 (c.M + A.Jw) hJ le_rfl).2.1
  have hτ := Velocity.Jets.ocTauP_pos (α := c.D.α) (q := c.D.q) (m := c.M + A.Jw) hΛ
  have ha : r.a < r.tq (c.M + A.Jw) := by
    have := r.reduction.1
    linarith
  have hT := weakRun_tq_le_window r hJ le_rfl
  obtain ⟨Dθ, hθ⟩ := r.scalar
  obtain ⟨u', w', hsol, hval⟩ := Reduction.weak_identification_core hb
    (show Applications.IsWeakSolutionOnWith _ _ _ _ _ _ Dθ from hθ) ha hT
  refine ⟨u', w', hsol, fun v t ht => ?_⟩
  have hv : v.1 = ⟨0, []⟩ := by
    exact Finset.mem_singleton.1
      ((Finset.ext_iff.1 (c.construction.2.1).2.1 v.1).1 v.2)
  have hr : (⟨0, []⟩ : Comp) ∈ (c.stage (c.M + A.Jw)).comps := hv ▸ v.2
  have hvv : v = ⟨_, hr⟩ := Subtype.ext hv
  have hrt := (r.reduction.2.2.1 hr t ⟨by
    have := r.reduction.1
    linarith [ht.1, hstep, hτ], ht.2⟩)
  subst hvv
  apply torusHk_ext_of_value_jet_ae
  have hjet := KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.zero_le R.Kw)
    (r.Ur (c.M + A.Jw) ⟨_, hr⟩ t) (valueIndex2 0)
  filter_upwards [hjet, hval t ht, hrt] with x h1 h2 h3
  change (truncateTorusHk (Nat.zero_le R.Kw) (r.Ur (c.M + A.Jw) ⟨_, hr⟩ t)).toFunction.jet
    (valueIndex2 0) x = _
  rw [h1, truncate_valueIndex_root, h3, ← h2]

section Row

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)]

/-- A scalar row (the coupled system with one component and no coupling) is a kernel-regularized
solution of any system without edges, with the same value at every component. -/
theorem kernelWeakSolutionTorus_of_row (hempty : ∀ i j, IsEmpty (Γ i j)) (ν t₀ t₁ : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (D D' : ℕ)
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => E)))
    (C : ∀ i j (α : Γ i j), E →L[ℝ] G i j α)
    (S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)))
    (u : ℝ → TorusHk 0 E) (w : ℝ → TorusHk (0 + 1) E) (ut : ι → ℝ → TorusHk 0 E)
    (hut : ∀ i, ∀ t ∈ Set.Icc t₀ t₁, ut i t = u t)
    (hsol : Providers.WeakGen.Comparison.IsTorusForcedRow ν t₀ t₁ v D' 0 (u t₀) (fun _ => 0)
      (fun _ => 0) u w) :
    IsKernelWeakSolutionTorus (ι := ι) (h := fun _ => E) (Γ := Γ) (G := G) ν t₀ t₁ v 0 D B C S
      (fun i => ut i t₀) (fun _ _ => 0) (fun _ _ => 0) ut (fun _ s => w s)
      (fun i j α _ => (hempty i j).elim α) := by
  refine ⟨fun i => (hsol.1 0).congr fun t ht => hut i t ht, fun i => hsol.2.1 0, ?_, ?_,
    fun i j α => (hempty i j).elim α, fun i j α => (hempty i j).elim α, ?_⟩
  · intro i
    filter_upwards [hsol.2.2.1 0, ae_restrict_mem measurableSet_Icc] with s hs hsI
    rw [hut i s hsI]
    exact hs
  · intro i
    rfl
  · intro i t ht φ
    have hc := hsol.2.2.2.2 0 t ht φ
    have : ∀ i j, IsEmpty (Γ i j) := hempty
    refine coupledWeakIdentity_data_eq (hut i t ht) (hut i t₀ ⟨le_rfl, ht.1.trans ht.2⟩) ?_ hc
    funext s x
    simp [Finset.univ_eq_empty]

end Row

/-- **Incoming passage at the root level `i = M + J_w`.** -/
theorem weakIncoming_root {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) :
    ∃ (w : ∀ v : CompIn (c.stage (c.M + A.Jw)).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root))
      (Y : ∀ v u (_ : (c.stage (c.M + A.Jw)).fam.Γ v u), ℝ →
        TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root)),
      WeakErrSol c r (c.M + A.Jw) (weakIncomingInit r (c.M + A.Jw)) (fun _ _ => 0)
        (fun _ _ => 0) (weakIncomingVal r (c.M + A.Jw)) w Y := by
  obtain ⟨u', w', hsol, hval⟩ := weakIncoming_root_scalar c r
  have hJ : (c.M < c.M + A.Jw) := by have := A.Jw_pos; omega
  have hT := weakRun_tq_le_window r hJ le_rfl
  have hempty : ∀ v u, IsEmpty ((c.stage (c.M + A.Jw)).fam.Γ v u) :=
    (c.construction.2.1).2.2.1
  refine ⟨fun _ t => w' t, fun v u γ t => (hempty v u).elim γ, ?_⟩
  unfold WeakErrSol
  exact kernelWeakSolutionTorus_of_row (E := ℝ) hempty _ _ _ _ _ 2 _ _ _ u' w'
    (weakIncomingVal r (c.M + A.Jw)) (fun v t ht => hval v t ht) hsol

end AVRegularity.Providers.WeakGen.Residual
end

section
namespace AVRegularity.Providers.WeakGen.Residual

/-! **`WeakIncomingRegStatement`**, from the passage case below the root and the
root case. -/

open WeakEntryProofs WeakEntryProofs.Assembly

/-- **Incoming regularity.** -/
theorem weakIncomingReg (plan : WeakPassagePlan) : WeakIncomingRegStatement plan := by
  intro B A R c r i hi hit
  rcases lt_or_eq_of_le hit with h | h
  · obtain ⟨Y, hY⟩ := weakIncoming_passage c r hi h
    exact ⟨weakIncomingLift r i, Y, hY⟩
  · subst h
    exact weakIncoming_root c r

end AVRegularity.Providers.WeakGen.Residual
end
