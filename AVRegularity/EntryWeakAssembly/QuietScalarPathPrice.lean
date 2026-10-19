-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Ingredients.ForcedEnergy.ComponentStrong
import AVRegularity.EntryWeakAssembly.QuietPassageRows
import AVRegularity.CycleJoint.Assembly.PatchBridges
public import AVRegularity.EntryWeakAssembly.Assembly.WeakEntryPairedForcing
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarTorusH1Time
import AVRegularity.CycleComparison.Coarse.Energy.Word
import AVRegularity.CycleComparison.Error.WeakSolution
public import AVRegularity.EntryWeakAssembly.QuietMarginPlan

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs

/-! **The paired difference, step 1: the forced energy of the paired system of `Gw`.**
A weak solution of the coupled system of `weakPairedOp` with zero data and forcing `F` plus the
paired flux has strong energy at most `√((24/κ_M) ∫ |F|²_{ρ_M})`
(`kernelForcedWeakSolution_forced_strongEnergy` with the drift data of the stream). -/

open AVRegularity.WeakEntryProofs.Assembly AVRegularity.KernelEnergy

section Forced

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}

/-- **The forced energy of the paired system of `Gw`** (zero data, forcing `F` and zero source). -/
theorem pd_forced_strongEnergy (hcommon : WeakEntryCommonOK plan)
    (hok : WeakEntryPairedPlanOK plan) {x : WeakEntryData plan C} (g : WeakEntryStages x)
    (s : WeakEntrySchedule g) (law : BirthLaw) (hm : law.rootMass = g.rootM)
    (F : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk R.Kw (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (hF : ∀ v, MemLp (F v) 2 (volume.restrict (Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀))))
    (U : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk R.Kw (ScalarH v.1.root))
    (W : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk (R.Kw + 1) (ScalarH v.1.root))
    (hsol : IsCoupledWeakSolutionTorus (x.D.κ x.M) (s.tq (x.M + 1)) (x.a + A.T₀)
      (streamVel (x.D.Φ x.M)) 0 (fun _ => R.Kw) TorusKernelOperator.noLocalCoefficient
      (fun _ => 0)
      (fun v t => F v t + (weakPairedOp hcommon hok g s law hm).carrierFlux W v t)
      (fun _ _ => 0) U W) :
    strongEnergy (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M) (g.Gw.mass law)
        (s.tq (x.M + 1)) (x.a + A.T₀) U W ≤
      ENNReal.ofReal (Real.sqrt ((24 / x.D.κ x.M) *
        ∫ t in Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀),
          massNormSq (x.D.termRStar (plan.radius R) x.M) (g.Gw.mass law)
            (fun v => (F v t).val))) := by
  let P := weakPairedOp hcommon hok g s law hm
  have hφ := Velocity.streamSeq_admissible B.hζ x.base128 x.streams x.M
  obtain ⟨hsmall, hstrain⟩ := weakPaired_drift hok x
  have hα : 0 ≤ Construction.Preservation.Buffer.actualDriftJetConstant * ocA B.α B.q A.Λ x.M :=
    mul_nonneg Construction.Preservation.Buffer.actualDriftJetConstant_nonneg
      (Real.rpow_pos_of_pos (weakPaired_eps_pos x) _).le
  obtain ⟨hv, hp, hd, ⟨V, hV⟩, hmeas⟩ := Construction.Preservation.Buffer.stream_kernel_drift_data
    hφ (s.tq (x.M + 1)) (x.a + A.T₀)
  have hV0 : 0 ≤ max V 0 := le_max_right _ _
  have hbV : ∀ t ∈ Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀), ∀ y, ‖streamVel (x.D.Φ x.M) t y‖ ≤
      max V 0 := fun t ht y => (hV t ht y).trans (le_max_left _ _)
  have hjets := weakPaired_jets hcommon x (s.tq (x.M + 1)) (x.a + A.T₀)
  have hg : ∀ v : CompIn g.Gw.comps, Integrable (fun _ : ℝ => (0 : TorusHk R.Kw (ScalarH v.1.root)))
      (volume.restrict (Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀))) := fun v => by
    show Integrable (0 : ℝ → TorusHk R.Kw (ScalarH v.1.root))
      (volume.restrict (Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀)))
    exact integrable_zero ℝ (TorusHk R.Kw (ScalarH v.1.root)) _
  have hmain := P.kernelForcedWeakSolution_forced_strongEnergy (streamVel (x.D.Φ x.M)) hv hp F
    (fun _ _ => 0) _ 1024 _ hα (by norm_num) (weakPaired_eps_pos x) hsmall hstrain hd hjets
    hmeas (max V 0) hV0 hbV (fun _ => driftCarrierBudget R.Kw (max V 0) _ 1024 _)
    (fun t ht _ => driftCarrierBudget_bounds R.Kw (streamVel (x.D.Φ x.M) t) (max V 0) _ 1024 _ hV0
      (hbV t ht) (hjets t ht)) W U (fun _ => 0) hF hg hsol
  refine hmain.trans (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_))
  have h0 : ∀ v : CompIn g.Gw.comps, factorialNormSq (x.D.termRStar (plan.radius R) x.M)
      ((0 : TorusHk R.Kw (ScalarH v.1.root)).val) = 0 :=
    fun v => CycleComparison.Coarse.factorialNormSq_zero_jet _
  have hz : massNormSq (x.D.termRStar (plan.radius R) x.M) P.π
      (fun v : CompIn g.Gw.comps => ((0 : TorusHk R.Kw (ScalarH v.1.root)).val)) = 0 :=
    Finset.sum_eq_zero fun v _ => by rw [h0 v, mul_zero]
  simp only [hz, Real.sqrt_zero, integral_zero]
  simp only [mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  exact le_of_eq rfl

end Forced

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Finite source-path algebra for the transposed quiet margin equation. Integrals
are commuted only after integrability of the actual native walk integrand is
supplied. No spatial coefficient norm or record weight replaces that integrand. -/

variable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}

/-- An insertion followed by backward propagation commutes with lowering
the available reserve. Both operations are the actual native operators. -/
theorem weak_quiet_insertion_propagated_lower (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x)
    (v u : x.Vertex) {P Q K L : ℕ} (hPQ : P ≤ Q) (hQL : Q + x.order ≤ L)
    (hPK : P + x.order ≤ K) (hKL : K ≤ L) (hL : L ≤ x.cap)
    (t b : ℝ) (ht : x.left ≤ t) (htb : t ≤ b) (hb : b ≤ x.right)
    (φ : TorusHk L ℝ) :
    truncateTorusHk hPQ
      (S.apply v u Q (hQL.trans hL) t
        (truncateTorusHk hQL (H.apply L t b φ))) =
      S.apply v u P ((hPK.trans hKL).trans hL) t
        (truncateTorusHk hPK (H.apply K t b (truncateTorusHk hKL φ))) := by
  rw [← weak_quiet_backward_truncate x hd H hKL hL t b ht htb hb φ,
    weak_quiet_insertion_truncate x S v u hPQ (hQL.trans hL) t
      ⟨ht, htb.trans hb⟩]
  rfl

/-- The exact n-insertion layer, paired with the actual entrance rows. -/
def weakQuietPathLayer (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x)
    (V : x.Vertex → TorusHk 0 ℝ) (n : ℕ) (hn : n ≤ prices.depth x.R)
    (v : x.Vertex) (a b : ℝ) (φ : TorusHk (n * x.order) ℝ) : ℝ :=
  ∑ u, ∑ π : WeakQuietWalk x.Vertex n v u,
    inner ℝ (V u) (weakQuietWalkDual x S H n hn v u π a b φ)

/-- Summing zero-length vertex walks selects precisely the unchanged vertex. -/
theorem weak_quiet_path_layer_zero (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x)
    (V : x.Vertex → TorusHk 0 ℝ) (v : x.Vertex) (a b : ℝ)
    (φ : TorusHk (0 * x.order) ℝ) :
    weakQuietPathLayer x S H V 0 (Nat.zero_le _) v a b φ =
      inner ℝ (V v) (H.apply 0 a b (truncateTorusHk (by simp) φ)) := by
  classical
  have hw (u : x.Vertex) :
      (∑ π : WeakQuietWalk x.Vertex 0 v u,
        inner ℝ (V u) (weakQuietWalkDual x S H 0 (Nat.zero_le _) v u π a b φ)) =
      if v = u then inner ℝ (V u) (H.apply 0 a b (truncateTorusHk (by simp) φ)) else 0 := by
    by_cases h : v = u
    · subst u
      let : Subsingleton (WeakQuietWalk x.Vertex 0 v v) := by
        change Subsingleton (PLift (v = v))
        infer_instance
      let : Unique (WeakQuietWalk x.Vertex 0 v v) :=
        ⟨⟨PLift.up rfl⟩, fun π => Subsingleton.elim _ _⟩
      simp only [weakQuietWalkDual, Finset.univ_unique, Finset.sum_singleton, ite_true]
    · let : IsEmpty (WeakQuietWalk x.Vertex 0 v u) := ⟨fun π => h π.down⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty, h, ite_false]
  unfold weakQuietPathLayer
  simp_rw [hw]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- One source-path layer is the sum of its actual one-insertion integrals.
This is the finite time-ordered identity used to unroll Duhamel. -/
theorem weak_quiet_path_layer_succ (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x)
    (V : x.Vertex → TorusHk 0 ℝ) (n : ℕ) (hn : n + 1 ≤ prices.depth x.R)
    (v : x.Vertex) (a b : ℝ) (φ : TorusHk ((n + 1) * x.order) ℝ)
    (hI : ∀ w u (π : WeakQuietWalk x.Vertex n w u),
      IntervalIntegrable (fun t => weakQuietWalkDual x S H n (by omega) w u π a t
        (S.apply v w (n * x.order)
          (by simpa only [Nat.succ_mul] using x.path_reserve (n + 1) hn) t
          (truncateTorusHk (by rw [Nat.succ_mul]) (H.apply ((n + 1) * x.order) t b φ))))
        volume a b) :
    weakQuietPathLayer x S H V (n + 1) hn v a b φ =
      ∑ w, ∫ t in a..b, weakQuietPathLayer x S H V n (by omega) w a t
        (S.apply v w (n * x.order)
          (by simpa only [Nat.succ_mul] using x.path_reserve (n + 1) hn) t
          (truncateTorusHk (by rw [Nat.succ_mul]) (H.apply ((n + 1) * x.order) t b φ))) := by
  classical
  let g (w u : x.Vertex) (π : WeakQuietWalk x.Vertex n w u) (t : ℝ) :=
    weakQuietWalkDual x S H n (by omega) w u π a t
      (S.apply v w (n * x.order)
        (by simpa only [Nat.succ_mul] using x.path_reserve (n + 1) hn) t
        (truncateTorusHk (by rw [Nat.succ_mul]) (H.apply ((n + 1) * x.order) t b φ)))
  have hpair (w u : x.Vertex) (π : WeakQuietWalk x.Vertex n w u) :
      IntervalIntegrable (fun t => inner ℝ (V u) (g w u π t)) volume a b :=
    ⟨(innerSL ℝ (V u)).integrable_comp (hI w u π).1,
      (innerSL ℝ (V u)).integrable_comp (hI w u π).2⟩
  have hw (u : x.Vertex) :
      (∑ π : WeakQuietWalk x.Vertex (n + 1) v u,
        inner ℝ (V u) (weakQuietWalkDual x S H (n + 1) hn v u π a b φ)) =
      ∑ w, ∑ π : WeakQuietWalk x.Vertex n w u, ∫ t in a..b,
        inner ℝ (V u) (g w u π t) := by
    let e : WeakQuietWalk x.Vertex (n + 1) v u ≃
        (Σ w : x.Vertex, WeakQuietWalk x.Vertex n w u) := Equiv.refl _
    calc
      _ = ∑ π : (Σ w : x.Vertex, WeakQuietWalk x.Vertex n w u),
          inner ℝ (V u) (∫ t in a..b, g π.1 u π.2 t) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro w _
        apply Finset.sum_congr rfl
        intro π _
        exact ((innerSL ℝ (V u)).intervalIntegral_comp_comm (hI w u π)).symm
  unfold weakQuietPathLayer
  simp_rw [hw]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  symm
  rw [intervalIntegral.integral_finsetSum (fun u _ => by
    have hi := IntervalIntegrable.sum Finset.univ (fun π _ => hpair w u π)
    have he : (∑ π : WeakQuietWalk x.Vertex n w u,
        fun t => inner ℝ (V u) (g w u π t)) =
        (fun t => ∑ π : WeakQuietWalk x.Vertex n w u,
          inner ℝ (V u) (g w u π t)) :=
      funext fun t => Finset.sum_apply t Finset.univ _
    rw [he] at hi
    exact hi)]
  apply Finset.sum_congr rfl
  intro u _
  exact intervalIntegral.integral_finsetSum (fun π _ => hpair w u π)

/-- The next-layer path integrands remain integrable after pairing and the
finite sum over their entrance vertices. -/
theorem weak_quiet_path_layer_source_integrable
    (x : WeakQuietExpansionCase plan prices) (S : WeakQuietInsertionData x)
    (H : WeakQuietBackwardEvolution x) (hI : WeakQuietWalkIntegrable x S H)
    (V : x.Vertex → TorusHk 0 ℝ) (n : ℕ) (hn : n + 1 ≤ prices.depth x.R)
    (v w : x.Vertex) (a b : ℝ) (ha : x.left ≤ a) (hab : a ≤ b) (hb : b ≤ x.right)
    (φ : TorusHk ((n + 1) * x.order) ℝ) :
    IntervalIntegrable (fun t => weakQuietPathLayer x S H V n (by omega) w a t
      (S.apply v w (n * x.order)
        (by simpa only [Nat.succ_mul] using x.path_reserve (n + 1) hn) t
        (truncateTorusHk (by rw [Nat.succ_mul]) (H.apply ((n + 1) * x.order) t b φ))))
      volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  exact integrable_finsetSum Finset.univ fun u _ =>
    integrable_finsetSum Finset.univ fun π _ =>
      (innerSL ℝ (V u)).integrable_comp (hI n hn v u ⟨w, π⟩ a b ha hab hb φ)

/-- All source paths through a finite insertion depth, acting on one common
high test reserve. The test is lowered for each shorter path. -/
def weakQuietPathPartial (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x)
    (V : x.Vertex → TorusHk 0 ℝ) (N : ℕ) (hN : N ≤ prices.depth x.R)
    (v : x.Vertex) (a b : ℝ) (φ : TorusHk (N * x.order) ℝ) : ℝ :=
  ∑ k : Fin (N + 1), weakQuietPathLayer x S H V k.val
    ((Nat.le_of_lt_succ k.isLt).trans hN) v a b
    (truncateTorusHk (Nat.mul_le_mul_right x.order (Nat.le_of_lt_succ k.isLt)) φ)

/-- The finite source-path sum obeys the same transposed one-step recurrence
as the triangular row system. Every exchange of sums with time integration
uses the analytic integrability of the actual path integrands. -/
theorem weak_quiet_path_partial_succ (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x)
    (hI : WeakQuietWalkIntegrable x S H) (V : x.Vertex → TorusHk 0 ℝ)
    (n : ℕ) (hn : n + 1 ≤ prices.depth x.R) (v : x.Vertex)
    (a b : ℝ) (ha : x.left ≤ a) (hab : a ≤ b) (hb : b ≤ x.right)
    (φ : TorusHk ((n + 1) * x.order) ℝ) :
    weakQuietPathPartial x S H V (n + 1) hn v a b φ =
      inner ℝ (V v) (H.apply 0 a b (truncateTorusHk (Nat.zero_le _) φ)) +
      ∑ w, ∫ t in a..b, weakQuietPathPartial x S H V n (by omega) w a t
        (S.apply v w (n * x.order)
          (by simpa only [Nat.succ_mul] using x.path_reserve (n + 1) hn) t
          (truncateTorusHk (by rw [Nat.succ_mul]) (H.apply ((n + 1) * x.order) t b φ))) := by
  classical
  let Vtest (k : Fin (n + 1)) : TorusHk ((k.val + 1) * x.order) ℝ :=
    truncateTorusHk (Nat.mul_le_mul_right x.order
      (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt))) φ
  let g (k : Fin (n + 1)) (w : x.Vertex) (t : ℝ) :=
    weakQuietPathLayer x S H V k.val (by omega) w a t
      (S.apply v w (k.val * x.order)
        (by have hh := x.path_reserve (k.val + 1) (by omega)
            simpa only [Nat.succ_mul] using hh) t
        (truncateTorusHk (by rw [Nat.succ_mul])
          (H.apply ((k.val + 1) * x.order) t b (Vtest k))))
  have hg (k : Fin (n + 1)) (w : x.Vertex) :
      IntervalIntegrable (g k w) volume a b :=
    weak_quiet_path_layer_source_integrable x S H hI V k.val (by omega)
      v w a b ha hab hb (Vtest k)
  have hstep (k : Fin (n + 1)) :
      weakQuietPathLayer x S H V (k.val + 1) (by omega) v a b (Vtest k) =
      ∑ w, ∫ t in a..b, g k w t := by
    apply weak_quiet_path_layer_succ
    intro w u π
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (hI k.val (by omega) v u ⟨w, π⟩ a b ha hab hb (Vtest k))
  unfold weakQuietPathPartial
  rw [Fin.sum_univ_succ]
  change weakQuietPathLayer x S H V 0 _ v a b _ +
    (∑ k : Fin (n + 1), weakQuietPathLayer x S H V (k.val + 1) _ v a b (Vtest k)) = _
  erw [weak_quiet_path_layer_zero]
  apply congrArg (fun z => inner ℝ (V v)
    (H.apply 0 a b (truncateTorusHk (Nat.zero_le _) φ)) + z)
  simp_rw [hstep]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [← intervalIntegral.integral_finsetSum (fun k _ => hg k w)]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [Set.uIoc_of_le hab]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg (weakQuietPathLayer x S H V k.val (by omega) w a t)
  exact (weak_quiet_insertion_propagated_lower x hd S H v w
    (Nat.mul_le_mul_right x.order (Nat.le_of_lt_succ k.isLt))
    (by rw [Nat.succ_mul]) (by rw [Nat.succ_mul])
    (Nat.mul_le_mul_right x.order (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)))
    (x.path_reserve (n + 1) hn) t b (ha.trans ht.1.le) ht.2 hb φ).symm

/-- The actual one-step transposed Duhamel identity, at every finite reserve
and every closed heat-quiet margin endpoint. It is the native row equation, with
its literal aggregate insertion and mass-conjugated row values. -/
def WeakQuietMovingRows (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x) : Prop :=
  ∀ n (hn : n + 1 ≤ prices.depth x.R) (v : x.Vertex) b,
    b ∈ Set.Icc x.left x.right → ∀ φ : TorusHk ((n + 1) * x.order) ℝ,
    inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v b))
      (truncateTorusHk (Nat.zero_le _) φ) =
    inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v x.left))
      (H.apply 0 x.left b (truncateTorusHk (Nat.zero_le _) φ)) +
    ∑ w, ∫ t in x.left..b,
      inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value w t))
        (truncateTorusHk (Nat.zero_le (n * x.order))
          (S.apply v w (n * x.order)
            (by simpa only [Nat.succ_mul] using x.path_reserve (n + 1) hn) t
            (truncateTorusHk (by rw [Nat.succ_mul])
              (H.apply ((n + 1) * x.order) t b φ))))

private theorem weakQuiet_root_no_edge (x : WeakQuietExpansionCase plan prices)
    (htop : x.i = x.c.M + x.A.Jw) :
    ∀ v u : x.Vertex, ¬ Nonempty ((x.c.stage x.i).fam.Γ v u) := by
  classical
  obtain ⟨hcomp, hΓ⟩ := EntryWeakProofs.weakConstruction_rank_bounds
    _ _ _ _ _ _ _ x.c.construction x.i x.level_lt.le x.level_le
  rintro v u ⟨γ⟩
  have hv := hcomp v.1 v.2
  have he := hΓ v u γ
  change EntryWeakProofs.weakComponentRank v.1 ≤
    (x.c.M + x.A.Jw - x.i) * x.A.Rw at hv
  have hz : x.c.M + x.A.Jw - x.i = 0 := Nat.sub_eq_zero_of_le htop.ge
  rw [hz, Nat.zero_mul] at hv
  omega

private theorem weakQuiet_zero_backward_pair {ν ρ a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} (hab : a ≤ b)
    (hd : WeakScalarTorusDrift ν ρ a b v 0)
    {f g : TorusHk 0 ℝ} {u z : ℝ → TorusHk 0 ℝ} {w zw : ℝ → TorusHk 1 ℝ}
    (hs : WeakScalarTorusSolution ν a b v 0 f u w)
    (hz : WeakScalarTorusSolution ν (-b) (-a) (fun t y => -v (-t) y) 0 g z zw) :
    inner ℝ (u b) g = inner ℝ (u a) (z (-a)) := by
  have hh := weak_scalar_adjoint_pair (E := ℝ) 0 hab hd hs hz
  have hinit : z (-b) = g := hz.2.2.2.1 0
  rw [hinit, CycleJointProofs.Assembly.truncateTorusHk_self,
    CycleJointProofs.Assembly.truncateTorusHk_self] at hh
  exact hh

/-- Native homogeneous adjoint pairing for the actual root values, with
an arbitrary finite-reserve terminal test. -/
theorem weak_quiet_root_backward_pair
    (x : WeakQuietExpansionCase plan prices)
    (htop : x.i = x.c.M + x.A.Jw)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (H : WeakQuietBackwardEvolution x) (v : x.Vertex) {P : ℕ}
    (b : ℝ) (hb : b ∈ Set.Icc x.left x.right) (φ : TorusHk P ℝ) :
    inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.run.Ur x.i v b))
      (truncateTorusHk (Nat.zero_le P) φ) =
    inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.run.Ur x.i v x.left))
      (H.apply 0 x.left b (truncateTorusHk (Nat.zero_le P) φ)) := by
  let U : ℝ → TorusHk 0 ℝ :=
    fun t => truncateTorusHk (Nat.zero_le x.R.Kw) (x.run.Ur x.i v t)
  change inner ℝ (U b) (truncateTorusHk (Nat.zero_le P) φ) =
    inner ℝ (U x.left) (H.apply 0 x.left b (truncateTorusHk (Nat.zero_le P) φ))
  obtain ⟨w, hs⟩ := weak_quiet_root_native_row x htop v
  change WeakScalarTorusSolution (x.c.D.κ x.c.M) x.left x.right
    (streamVel (x.c.D.Φ (x.i - 1))) 0 (U x.left) U w at hs
  have hs' : WeakScalarTorusSolution (x.c.D.κ x.c.M) x.left b
      (streamVel (x.c.D.Φ (x.i - 1))) 0
      (U x.left) U w :=
    CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_left hb.2 hs
  obtain ⟨z, zw, hz, he⟩ := H.native 0 (Nat.zero_le _) x.left b le_rfl hb.1 hb.2
    (truncateTorusHk (Nat.zero_le _) φ)
  have hp := weakQuiet_zero_backward_pair hb.1
    (hd.restrict (Set.Icc_subset_Icc le_rfl hb.2) (Nat.zero_le _)) hs' hz
  rw [he]
  exact hp

/-- The edgeless root satisfies the actual moving-row identity on every
closed heat subwindow. Its own native scalar lift comes from identification,
while absence of all source identities follows from the construction rank. -/
theorem weak_quiet_root_moving_rows
    (x : WeakQuietExpansionCase plan prices)
    (htop : x.i = x.c.M + x.A.Jw)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x) :
    WeakQuietMovingRows x S H := by
  classical
  have hempty := weakQuiet_root_no_edge x htop
  intro n hn v b hb φ
  have hp := weak_quiet_root_backward_pair x htop hd H v b hb φ
  have hp0 : inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v b))
      (truncateTorusHk (Nat.zero_le _) φ) =
      inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v x.left))
        (H.apply 0 x.left b (truncateTorusHk (Nat.zero_le _) φ)) := by
    simp only [WeakQuietExpansionCase.value, map_smul, real_inner_smul_left]
    rw [hp]
  rw [hp0]
  symm
  apply add_eq_left.mpr
  apply Finset.sum_eq_zero
  intro u _
  calc
    _ = ∫ _t in x.left..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hb.1] at ht
      dsimp only
      rw [weak_quiet_insertion_zero_of_no_edge x S v u (hempty v u) _ _ t
        ⟨ht.1, ht.2.trans hb.2⟩, ContinuousLinearMap.map_zero, inner_zero_right]
    _ = 0 := intervalIntegral.integral_zero

/-- Every finite source-path sum vanishes on the zero test. -/
theorem weak_quiet_path_partial_zero (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x)
    (V : x.Vertex → TorusHk 0 ℝ) (n : ℕ) (hn : n ≤ prices.depth x.R)
    (v : x.Vertex) (a b : ℝ) (ha : x.left ≤ a) (hab : a ≤ b) (hb : b ≤ x.right) :
    weakQuietPathPartial x S H V n hn v a b 0 = 0 := by
  classical
  unfold weakQuietPathPartial weakQuietPathLayer
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro π _
  rw [ContinuousLinearMap.map_zero,
    weak_quiet_walk_dual_zero x hd S H k.val _ v u π a b ha hab hb, inner_zero_right]

/-- Finite downward induction in the actual triangular rank identifies every
row with the source-path sum. The induction uses only shorter actual edges;
a nontriangular majorant matrix is allowed throughout. -/
theorem weak_quiet_path_partial_of_moving_rows
    (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x)
    (hI : WeakQuietWalkIntegrable x S H) (hrow : WeakQuietMovingRows x S H)
    (n : ℕ) (hn : n ≤ prices.depth x.R) (v : x.Vertex)
    (hv : EntryWeakProofs.weakComponentRank v.1 < n)
    (b : ℝ) (hb : b ∈ Set.Icc x.left x.right) (φ : TorusHk (n * x.order) ℝ) :
    inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v b))
      (truncateTorusHk (Nat.zero_le _) φ) =
    weakQuietPathPartial x S H
      (fun u => truncateTorusHk (Nat.zero_le x.R.Kw) (x.value u x.left))
      n hn v x.left b φ := by
  classical
  obtain ⟨_, hΓ⟩ := EntryWeakProofs.weakConstruction_rank_bounds
    _ _ _ _ _ _ _ x.c.construction x.i x.level_lt.le x.level_le
  induction n generalizing v b with
  | zero => omega
  | succ n ih =>
    rw [hrow n hn v b hb φ,
      weak_quiet_path_partial_succ x hd S H hI _ n hn v x.left b le_rfl hb.1 hb.2 φ]
    apply congrArg (fun z => inner ℝ
      (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v x.left))
      (H.apply 0 x.left b (truncateTorusHk (Nat.zero_le _) φ)) + z)
    apply Finset.sum_congr rfl
    intro w _
    apply intervalIntegral.integral_congr_ae_restrict
    rw [Set.uIoc_of_le hb.1]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    by_cases hedge : Nonempty ((x.c.stage x.i).fam.Γ v w)
    · obtain ⟨γ⟩ := hedge
      have hw : EntryWeakProofs.weakComponentRank w.1 < n := by
        have hh := hΓ v w γ
        omega
      exact ih (by omega) w hw t ⟨ht.1.le, ht.2.trans hb.2⟩ _
    · rw [weak_quiet_insertion_zero_of_no_edge x S v w hedge _ _ t
        ⟨ht.1.le, ht.2.trans hb.2⟩, ContinuousLinearMap.map_zero, inner_zero_right]
      exact (weak_quiet_path_partial_zero x hd S H _ n (by omega) w x.left t
        le_rfl ht.1.le (ht.2.trans hb.2)).symm

/-- The fixed depth condition closes the finite expansion at the actual
terminal time. There is no remainder, including for an edgeless root. -/
theorem weak_quiet_ordered_paths_of_moving_rows
    (hdepth : WeakQuietMarginDepthOK plan prices)
    (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x)
    (hI : WeakQuietWalkIntegrable x S H) (hrow : WeakQuietMovingRows x S H)
    (v : x.Vertex) (φ : TorusHk x.cap ℝ) :
    inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v x.right))
      (truncateTorusHk (Nat.zero_le x.cap) φ) =
    ∑ u, ∑ n : Fin (prices.depth x.R + 1),
      ∑ π : WeakQuietWalk x.Vertex n.val v u,
        inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value u x.left))
          (weakQuietWalkDual x S H n.val (Nat.le_of_lt_succ n.isLt)
            v u π x.left x.right
            (truncateTorusHk (x.path_reserve n.val (Nat.le_of_lt_succ n.isLt)) φ)) := by
  classical
  obtain ⟨hcomp, _⟩ := EntryWeakProofs.weakConstruction_rank_bounds
    _ _ _ _ _ _ _ x.c.construction x.i x.level_lt.le x.level_le
  have hrank := hcomp v.1 v.2
  change EntryWeakProofs.weakComponentRank v.1 ≤
    (x.c.M + x.A.Jw - x.i) * x.A.Rw at hrank
  have hmenu : (x.c.M + x.A.Jw - x.i) * x.A.Rw ≤ x.A.Jw * x.A.Rw :=
    Nat.mul_le_mul_right x.A.Rw (by have hi := x.level_lt; omega)
  have hv : EntryWeakProofs.weakComponentRank v.1 < prices.depth x.R := by
    have hh := (hdepth x.R).1
    omega
  have he := weak_quiet_path_partial_of_moving_rows x hd S H hI hrow
    (prices.depth x.R) le_rfl v hv x.right ⟨x.heat_window.1.le, le_rfl⟩
    (truncateTorusHk (x.path_reserve (prices.depth x.R) le_rfl) φ)
  rw [Finset.sum_comm]
  exact he

end AVRegularity.WeakEntryProofs.Assembly
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleComparison.Coarse
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Actual mass-conjugated moving rows. Native source pairing identifies the
literal aggregate b insertion with the supplied width-zero kernel flux. -/

variable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}

private theorem weakQuiet_mass_ratio_cancel {μ π : ℝ} (hμ : 0 < μ) :
    (Real.sqrt μ)⁻¹ * Real.sqrt (μ / π) = (Real.sqrt π)⁻¹ := by
  rw [Real.sqrt_div hμ.le, div_eq_mul_inv, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hμ)), one_mul]

private theorem weakQuiet_normalize_pair {K : ℕ} {μ π q : ℝ} (hμ : 0 < μ)
    (u : TorusHk K ℝ) (ψ : TorusHk 0 ℝ)
    (hh : inner ℝ (truncateTorusHk (Nat.zero_le K) u) ψ = -Real.sqrt (μ / π) * q) :
    inner ℝ (truncateTorusHk (Nat.zero_le K) ((Real.sqrt μ)⁻¹ • u)) ψ =
      -(Real.sqrt π)⁻¹ * q := by
  rw [map_smul, real_inner_smul_left, hh, neg_mul, mul_neg, ← mul_assoc,
    weakQuiet_mass_ratio_cancel hμ, neg_mul]

private theorem weakQuiet_normalized_adjoint_pair {K m R Kc P : ℕ} {C μ π : ℝ}
    {T : (Vec 2 → ℝ) → Vec 2 → ℝ} (hμ : 0 < μ) (hm : 1 ≤ m)
    (Adj : TorusAdj T m R Kc C) (u : TorusHk K ℝ)
    (Q : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ))) (h0 : 0 + m ≤ Kc)
    (hpair : ∀ ψ : TorusHk (0 + m) ℝ,
      inner ℝ (truncateTorusHk (Nat.zero_le K) u) (Adj.adj 0 h0 ψ) =
      -Real.sqrt (μ / π) * inner ℝ (torusHkValueCLM Q)
        (torusH1GradientL2CLM (E := ℝ) (truncateTorusHk (by omega) ψ)))
    (hP : P + m ≤ Kc) (φ : TorusHk (P + m) ℝ) :
    inner ℝ (truncateTorusHk (Nat.zero_le K) ((Real.sqrt μ)⁻¹ • u))
      (truncateTorusHk (Nat.zero_le P) (Adj.adj P hP φ)) =
      -(Real.sqrt π)⁻¹ * inner ℝ (torusHkValueCLM Q)
        (torusH1GradientL2CLM (E := ℝ) (truncateTorusHk (by omega) φ)) := by
  apply weakQuiet_normalize_pair hμ
  rw [weak_quiet_formal_adjoint_truncate Adj (Nat.zero_le P) hP,
    hpair (truncateTorusHk (E := ℝ) (Nat.add_le_add_right (Nat.zero_le P) m) φ)]
  rfl

/-- Identify the order-zero source pairing with a supplied actual flux. -/
theorem weak_quiet_actual_incoming_pair_zero
    (hdepth : WeakQuietMarginDepthOK plan prices)
    (x : WeakQuietExpansionCase plan prices)
    (hfloor : weakComparisonCoeffFloor x.R ≤ x.c.M)
    (hhalf : 2 * plan.radius x.R ≤ 1) (S : WeakQuietInsertionData x)
    (v u : x.Vertex) (t : ℝ) (ht : t ∈ Set.Icc x.left x.right)
    (Y : (x.c.stage x.i).fam.Γ v u → TorusHk (x.R.Kw + x.c.Dm - 1) ℝ)
    (hu : ∀ γ, truncateTorusHk (Nat.zero_le _) (Y γ) =
      truncateTorusHk (Nat.zero_le x.R.Kw) (x.run.Ur x.i u t))
    (Q : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ)))
    (hQ : Q.toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun y =>
      ∑ γ : (x.c.stage x.i).fam.Γ v u, ∑ d : ↥(Finset.Icc 2 x.c.Dm),
        (x.c.stage x.i).physCoeff v u γ d.1 t y
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            (Y γ).toFunction.jet ⟨⟨d.1 - 1, by
              have := Finset.mem_Icc.mp d.2; omega⟩, word⟩ y))
 :
    ∀ (hP : 0 + x.order ≤ x.cap) (φ : TorusHk (0 + x.order) ℝ),
      inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.run.Ur x.i u t))
        (S.apply v u 0 hP t φ) =
      -Real.sqrt (x.mass u / x.mass v) * inner ℝ (torusHkValueCLM Q)
        (torusH1GradientL2CLM (E := ℝ)
          (truncateTorusHk (by unfold WeakQuietExpansionCase.order; omega) φ)) := by
  obtain ⟨F, hF, hpair⟩ := weak_quiet_actual_incoming_pair hdepth x hfloor hhalf
    S v u t ht Y (truncateTorusHk (E := ℝ) (Nat.zero_le x.R.Kw) (x.run.Ur x.i u t)) hu
  have he : F = Q := KernelEnergy.torusCarrier_eq_of_value_ae F Q (hF.trans hQ.symm)
  subst F
  exact hpair

/-- At every reserve, a genuine insertion is exactly the native incoming
flux pairing, after the prescribed mass conjugation. No derivative of the
actual order-zero row is postulated: Y supplies the actual high carriers. -/
theorem weak_quiet_actual_incoming_pair_lower
    (hdepth : WeakQuietMarginDepthOK plan prices)
    (x : WeakQuietExpansionCase plan prices)
    (hfloor : weakComparisonCoeffFloor x.R ≤ x.c.M)
    (hhalf : 2 * plan.radius x.R ≤ 1) (S : WeakQuietInsertionData x)
    (v u : x.Vertex) (t : ℝ) (ht : t ∈ Set.Icc x.left x.right)
    (Y : (x.c.stage x.i).fam.Γ v u → TorusHk (x.R.Kw + x.c.Dm - 1) ℝ)
    (hu : ∀ γ, truncateTorusHk (Nat.zero_le _) (Y γ) =
      truncateTorusHk (Nat.zero_le x.R.Kw) (x.run.Ur x.i u t))
    (Q : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ)))
    (hQ : Q.toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun y =>
      ∑ γ : (x.c.stage x.i).fam.Γ v u, ∑ d : ↥(Finset.Icc 2 x.c.Dm),
        (x.c.stage x.i).physCoeff v u γ d.1 t y
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            (Y γ).toFunction.jet ⟨⟨d.1 - 1, by
              have := Finset.mem_Icc.mp d.2; omega⟩, word⟩ y))
    {P : ℕ} (hP : P + x.order ≤ x.cap) (φ : TorusHk (P + x.order) ℝ) :
    inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value u t))
      (truncateTorusHk (Nat.zero_le P) (S.apply v u P hP t φ)) =
        -(Real.sqrt (x.mass v))⁻¹ * inner ℝ (torusHkValueCLM Q)
          (torusH1GradientL2CLM (E := ℝ)
            (truncateTorusHk (by unfold WeakQuietExpansionCase.order; omega) φ)) := by
  have hpair := weak_quiet_actual_incoming_pair_zero hdepth x hfloor hhalf S v u t ht Y hu Q hQ
  obtain ⟨C, Adj, he, _⟩ := S.adjoint v u t ht
  have h0 : 0 + x.order ≤ x.cap := by
    simpa only [Nat.zero_add] using (Nat.le_add_left x.order P).trans hP
  rw [he P hP]
  dsimp only [WeakQuietExpansionCase.value]
  rw [Real.sqrt_inv]
  apply weakQuiet_normalized_adjoint_pair (μ := x.mass u) (π := x.mass v)
    (x.mass_pos u) (by unfold WeakQuietExpansionCase.order; omega)
    Adj (x.run.Ur x.i u t) Q h0 ?_ hP φ
  intro ψ
  rw [← he 0 h0]
  exact hpair h0 ψ

/-- On a native backward trajectory, every actual normalized insertion is
almost everywhere its incoming flux-gradient pairing. The high incoming
carrier is identified by the actual width-zero kernel equation. -/
theorem weak_quiet_incoming_moving_pair
    (hdepth : WeakQuietMarginDepthOK plan prices)
    (x : WeakQuietExpansionCase plan prices)
    (hfloor : weakComparisonCoeffFloor x.R ≤ x.c.M)
    (hhalf : 2 * plan.radius x.R ≤ 1)
    (htop : x.i < x.c.M + x.A.Jw)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x)
    (v u : x.Vertex) {P : ℕ} (hP : P + x.order ≤ x.cap)
    (b : ℝ) (hb : b ∈ Set.Icc x.left x.right)
    {φ : TorusHk (P + x.order) ℝ}
    {z : ℝ → TorusHk (P + x.order) ℝ}
    {zw : ℝ → TorusHk (P + x.order + 1) ℝ}
    (hz : WeakScalarTorusSolution (x.c.D.κ x.c.M) (-b) (-x.left)
      (fun t y => -streamVel (x.c.D.Φ (x.i - 1)) (-t) y) (P + x.order) φ z zw)
    (Q : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ)))
    (hraw : ∀ t ∈ Set.Icc x.left x.right,
      (Q t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun y =>
        ∑ γ : (x.c.stage x.i).fam.Γ v u, ∑ d : ↥(Finset.Icc 2 x.c.Dm),
          (x.c.stage x.i).physCoeff v u γ d.1 t y
            (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
              (x.run.Urk x.i v u γ t).toFunction.jet
                ⟨⟨d.1 - 1, by have := Finset.mem_Icc.mp d.2; omega⟩, word⟩ y)) :
    (fun t => inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value u t))
      (truncateTorusHk (Nat.zero_le P)
        (S.apply v u P hP t (H.apply (P + x.order) t b φ)))) =ᵐ[
          volume.restrict (Set.Icc x.left b)]
      (fun t => -(Real.sqrt (x.mass v))⁻¹ *
        inner ℝ (torusHkValueCLM (Q t)) (torusH1GradientL2CLM (E := ℝ)
          (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (P + x.order))) (zw (-t))))) := by
  have htrace : ∀ᵐ t ∂volume.restrict (Set.Icc x.left b),
      truncateTorusHk (E := ℝ) (Nat.le_succ (P + x.order)) (zw (-t)) = z (-t) := by
    have hh := (CycleEvolution.cellTimeReverse_measurePreserving_Icc (-b) (-x.left)).quasiMeasurePreserving.ae (hz.2.2.1 0)
    simpa only [neg_neg] using hh
  have hinput : ∀ᵐ t ∂volume.restrict (Set.Icc x.left b),
      ∀ γ : (x.c.stage x.i).fam.Γ v u,
        truncateTorusHk (E := ℝ) (Nat.zero_le _) (x.run.Urk x.i v u γ t) =
          truncateTorusHk (E := ℝ) (Nat.zero_le x.R.Kw) (x.run.Ur x.i u t) := by
    apply ae_all_iff.mpr
    intro γ
    have hh := ae_restrict_of_ae_restrict_of_subset
      (Set.Icc_subset_Icc le_rfl hb.2) (weak_quiet_nonroot_input_value x htop v u γ)
    filter_upwards [hh] with t ht
    apply TorusHk.ext_value
    exact ht
  filter_upwards [htrace, hinput, ae_restrict_mem measurableSet_Icc] with t htr hu ht
  have htc : t ∈ Set.Icc x.left x.right := ⟨ht.1, ht.2.trans hb.2⟩
  rw [weak_quiet_backward_values x hd H hP le_rfl hb.2 hz t ht]
  rw [weak_quiet_actual_incoming_pair_lower hdepth x hfloor hhalf S v u t htc
    (fun γ => x.run.Urk x.i v u γ t) hu (Q t) (hraw t htc) hP]
  rw [← htr]
  rfl

/-- The actual nonroot equation supplies the full normalized Duhamel identity
at each native test reserve. Every source summand is integrable individually. -/
theorem weak_quiet_nonroot_backward_pair
    (hdepth : WeakQuietMarginDepthOK plan prices)
    (x : WeakQuietExpansionCase plan prices)
    (hfloor : weakComparisonCoeffFloor x.R ≤ x.c.M)
    (hhalf : 2 * plan.radius x.R ≤ 1)
    (htop : x.i < x.c.M + x.A.Jw)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x)
    (v : x.Vertex) {P : ℕ} (hP : P + x.order ≤ x.cap)
    (b : ℝ) (hb : b ∈ Set.Icc x.left x.right) (φ : TorusHk (P + x.order) ℝ) :
    inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v b))
        (truncateTorusHk (Nat.zero_le _) φ) =
      inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v x.left))
        (H.apply 0 x.left b (truncateTorusHk (Nat.zero_le _) φ)) +
      ∑ u, ∫ t in x.left..b,
        inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value u t))
          (truncateTorusHk (Nat.zero_le P)
            (S.apply v u P hP t (H.apply (P + x.order) t b φ))) := by
  classical
  obtain ⟨Q, hQ, hraw⟩ := weak_quiet_nonroot_incoming_flux x hfloor htop
  let U : ℝ → TorusHk 0 ℝ :=
    fun t => truncateTorusHk (E := ℝ) (Nat.zero_le x.R.Kw) (x.run.Ur x.i v t)
  have hsumraw : ∀ t ∈ Set.Icc (x.run.tq (x.i + 1)) (x.run.a + x.A.T₀),
      (∑ u, Q v u t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
        weakQuietKernelRawFlux (x.c.stage x.i) (x.run.Urk x.i) v t := by
    intro t ht
    apply KernelEnergy.torusJet_sum_ae_of_eq
    intro u
    exact hraw v u t ht
  have hs := weak_quiet_nonroot_native_row x htop v (fun t => ∑ u, Q v u t) hsumraw
  change IsTorusForcedRow (x.c.D.κ x.c.M) x.left x.right
    (streamVel (x.c.D.Φ (x.i - 1))) 2 0 (U x.left)
    (fun t => ∑ u, Q v u t) (fun _ => 0) U _ at hs
  have hs' := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_left hb.2 hs
  obtain ⟨z, zw, hz, he⟩ := H.native (P + x.order) hP x.left b le_rfl hb.1 hb.2 φ
  have hQ' (u : x.Vertex) : MemLp (Q v u) 2 (volume.restrict (Set.Icc x.left b)) :=
    (hQ v u).mono_measure (Measure.restrict_mono
      (fun t ht => x.heat_window.2 ⟨ht.1, ht.2.trans hb.2⟩) le_rfl)
  have hpair := fun u => weak_quiet_incoming_moving_pair hdepth x hfloor hhalf htop hd
    S H v u hP b hb hz (Q v u) (fun t ht => hraw v u t (x.heat_window.2 ht))
  have hp := (weak_quiet_forced_sum_duhamel hb.1
    (hd.restrict (Set.Icc_subset_Icc le_rfl hb.2) hP) hQ' hs' hz hpair).2
  have hzero : H.apply 0 x.left b (truncateTorusHk (E := ℝ) (Nat.zero_le (P + x.order)) φ) =
      truncateTorusHk (E := ℝ) (Nat.zero_le (P + x.order)) (z (-x.left)) := by
    rw [← weak_quiet_backward_truncate x hd H (Nat.zero_le _) hP
      x.left b le_rfl hb.1 hb.2 φ, he]
  rw [hzero]
  simpa only [WeakQuietExpansionCase.value, Real.sqrt_inv, map_smul, real_inner_smul_left] using hp


/-- Both cases of the actual passage satisfy the full finite-reserve moving
row identity. The root uses the identified scalar lift; the nonroot uses its
separate native incoming fluxes and their individually integrable pairings. -/
theorem weak_quiet_moving_rows
    (hdepth : WeakQuietMarginDepthOK plan prices)
    (x : WeakQuietExpansionCase plan prices)
    (hfloor : weakComparisonCoeffFloor x.R ≤ x.c.M)
    (hhalf : 2 * plan.radius x.R ≤ 1)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x) :
    WeakQuietMovingRows x S H := by
  by_cases htop : x.i = x.c.M + x.A.Jw
  · exact weak_quiet_root_moving_rows x htop hd S H
  · have hlt : x.i < x.c.M + x.A.Jw := lt_of_le_of_ne x.level_le htop
    intro n hn v b hb φ
    have hL := x.path_reserve (n + 1) hn
    have hQL : n * x.order + x.order ≤ (n + 1) * x.order := by rw [Nat.succ_mul]
    have hP := hQL.trans hL
    have hh := weak_quiet_nonroot_backward_pair hdepth x hfloor hhalf hlt hd S H v
      hP b hb (truncateTorusHk (E := ℝ) hQL φ)
    have htest : truncateTorusHk (E := ℝ) (Nat.zero_le (n * x.order + x.order))
        (truncateTorusHk (E := ℝ) hQL φ) = truncateTorusHk (E := ℝ) (Nat.zero_le _) φ := rfl
    rw [htest] at hh
    rw [hh]
    apply congrArg (fun z => inner ℝ
      (truncateTorusHk (E := ℝ) (Nat.zero_le x.R.Kw) (x.value v x.left))
      (H.apply 0 x.left b (truncateTorusHk (E := ℝ) (Nat.zero_le _) φ)) + z)
    apply Finset.sum_congr rfl
    intro u _
    apply intervalIntegral.integral_congr_ae_restrict
    rw [Set.uIoc_of_le hb.1]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [← weak_quiet_backward_truncate x hd H hQL hL t b ht.1.le ht.2 hb.2 φ]

/-- Numerical conditions for the finite row unrolling. All depend only on
request-level choices, before M, Dm, the family, or the scalar datum. -/
structure WeakQuietRowsPlanOK (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) : Prop where
  depth : WeakQuietMarginDepthOK plan prices
  coeff : WeakComparisonCoeffPlanOK plan
  drift : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) j₀,
    weakQuietDriftFloor B A.Λ ≤ plan.levelFloor R j₀
  small : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    plan.radius R ≤ 1 / 2048

/-- Raise only the level threshold of the existing reserve/trace refinement
so that the actual incoming carriers have the required coefficient regularity. -/
def weakQuietRowsPlan (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) : WeakPassagePlan :=
  let base := weakQuietTracePlan (weakQuietReservePlan plan prices) prices
  { base with levelFloor := fun R j₀ => max (base.levelFloor R j₀) (weakComparisonCoeffFloor R) }

/-- The purely numerical row conditions are discharged by pre-data choices.
Neither the radius nor any scalar price is changed by this refinement. -/
theorem weak_quiet_rows_plan_spec (plan : WeakPassagePlan) (prices : WeakQuietPathPrices)
    (hsmall : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      plan.radius R ≤ 1 / 2048)
    (hdepth : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      A.Jw * A.Rw + 1 ≤ prices.depth R) : WeakQuietRowsPlanOK (weakQuietRowsPlan plan prices) prices := by
  refine ⟨(weak_quiet_margin_plan_spec plan prices).2.2.2.2 hdepth,
    fun R j₀ => Nat.le_max_right _ _, ?_, hsmall⟩
  intro B A R j₀
  exact ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans (Nat.le_max_left _ _)

/-- **Path expansion.** The actual triangular passage equations give the exact
finite ordered-path expansion. All analytical row inputs are discharged by
the native scalar identification, width-zero kernel equation, and drift budget.
Only the separate scalar-path integrability group is passed to finite summation. -/
theorem weak_quiet_ordered_paths (hok : WeakQuietRowsPlanOK plan prices) :
    WeakQuietOrderedPathsStatement plan prices := by
  intro x S H hI v φ
  obtain ⟨hd⟩ := weak_quiet_parent_drift x.c
    ((hok.drift x.R x.c.j₀).trans x.c.level_ge) (hok.small x.R)
    x.i x.level_lt x.left x.right x.cap
  have hfloor := (hok.coeff x.R x.c.j₀).trans x.c.level_ge
  have hhalf : 2 * plan.radius x.R ≤ 1 := by
    have hh := hok.small x.R
    linarith only [hh]
  exact weak_quiet_ordered_paths_of_moving_rows hok.depth x hd S H hI
    (weak_quiet_moving_rows hok.depth x hfloor hhalf hd S H) v φ

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Assembly

/-! The aggregate parent coefficient budget, converted to real source weights.
Every constituent is already known finite. The ambient order cap occurs only
in a finite sum, never in a constant or derivative reserve. -/

variable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}

/-- The literal dimensionless price of one constituent coefficient. -/
def weakQuietCoefficientWeight (x : WeakQuietExpansionCase plan prices) (v u : x.Vertex)
    (γ : (x.c.stage x.i).fam.Γ v u) (d : ℕ) : ℝ :=
  (coefficientSeminorm (x.c.D.eps (x.i - 1)) (plan.jetOrder x.R)
    x.left x.right ((x.c.stage x.i).physCoeff v u γ d)).toReal /
      (x.c.D.κ x.c.M * x.c.D.eps (x.i - 1) ^ (d - 2))

/-- Every constituent has nonnegative dimensionless weight. -/
theorem weak_quiet_coefficient_weight_nonneg (x : WeakQuietExpansionCase plan prices)
    (v u : x.Vertex) (γ : (x.c.stage x.i).fam.Γ v u) (d : ℕ) :
    0 ≤ weakQuietCoefficientWeight x v u γ d := by
  unfold weakQuietCoefficientWeight
  exact div_nonneg ENNReal.toReal_nonneg
    (mul_nonneg x.bounds.2.1.le (pow_nonneg x.bounds.1.le _))

/-- Normalization of a constituent is exact, including a zero coefficient. -/
theorem weak_quiet_coefficient_weight_identity (x : WeakQuietExpansionCase plan prices)
    (v u : x.Vertex) (γ : (x.c.stage x.i).fam.Γ v u) (d : ℕ) :
    x.c.D.κ x.c.M * x.c.D.eps (x.i - 1) ^ (d - 2) *
      weakQuietCoefficientWeight x v u γ d =
    (coefficientSeminorm (x.c.D.eps (x.i - 1)) (plan.jetOrder x.R)
      x.left x.right ((x.c.stage x.i).physCoeff v u γ d)).toReal := by
  unfold weakQuietCoefficientWeight
  exact mul_div_cancel₀ _ (ne_of_gt (mul_pos x.bounds.2.1 (pow_pos x.bounds.1 _)))

/-- The original ENNReal budget gives the real sum with precisely its mass
ratio and diffusivity normalization. -/
theorem weak_quiet_coefficient_weight_sum (x : WeakQuietExpansionCase plan prices)
    (v u : x.Vertex) :
    Real.sqrt (x.mass u / x.mass v) *
      (∑ γ : (x.c.stage x.i).fam.Γ v u, ∑ d ∈ Finset.Icc 2 x.c.Dm,
        weakQuietCoefficientWeight x v u γ d) ≤ x.b v u := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, hm⟩ := x.bounds
  have hfin (γ : (x.c.stage x.i).fam.Γ v u) (d : ℕ) (hd : d ∈ Finset.Icc 2 x.c.Dm) :
      coefficientSeminorm (x.c.D.eps (x.i - 1)) (plan.jetOrder x.R)
        x.left x.right ((x.c.stage x.i).physCoeff v u γ d) *
        (ENNReal.ofReal (x.c.D.κ x.c.M * x.c.D.eps (x.i - 1) ^ (d - 2)))⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (x.coefficient_finite v u γ d hd)
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr
        (mul_pos x.bounds.2.1 (pow_pos x.bounds.1 _))))
  have hs (γ : (x.c.stage x.i).fam.Γ v u) :
      (∑ d ∈ Finset.Icc 2 x.c.Dm,
        coefficientSeminorm (x.c.D.eps (x.i - 1)) (plan.jetOrder x.R)
          x.left x.right ((x.c.stage x.i).physCoeff v u γ d) *
          (ENNReal.ofReal (x.c.D.κ x.c.M * x.c.D.eps (x.i - 1) ^ (d - 2)))⁻¹) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (hfin γ)
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hm v u)
  change (ENNReal.ofReal (Real.sqrt (x.mass u / x.mass v)) *
    ∑ γ : (x.c.stage x.i).fam.Γ v u, ∑ d ∈ Finset.Icc 2 x.c.Dm,
      coefficientSeminorm (x.c.D.eps (x.i - 1)) (plan.jetOrder x.R)
        x.left x.right ((x.c.stage x.i).physCoeff v u γ d) *
        (ENNReal.ofReal (x.c.D.κ x.c.M * x.c.D.eps (x.i - 1) ^ (d - 2)))⁻¹).toReal ≤
      (ENNReal.ofReal (x.b v u)).toReal at hh
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_sum (fun γ _ => hs γ),
    ENNReal.toReal_ofReal (x.bounds.2.2.2.2.1 v u)] at hh
  have he (γ : (x.c.stage x.i).fam.Γ v u) :
      (∑ d ∈ Finset.Icc 2 x.c.Dm,
        coefficientSeminorm (x.c.D.eps (x.i - 1)) (plan.jetOrder x.R)
          x.left x.right ((x.c.stage x.i).physCoeff v u γ d) *
          (ENNReal.ofReal (x.c.D.κ x.c.M * x.c.D.eps (x.i - 1) ^ (d - 2)))⁻¹).toReal =
        ∑ d ∈ Finset.Icc 2 x.c.Dm, weakQuietCoefficientWeight x v u γ d := by
    rw [ENNReal.toReal_sum (hfin γ)]
    apply Finset.sum_congr rfl
    intro d _
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (mul_nonneg x.bounds.2.1.le (pow_nonneg x.bounds.1.le _))]
    rfl
  simp_rw [he] at hh
  exact hh

/-- Removing the physically zero orders leaves the same valid b budget. -/
theorem weak_quiet_coefficient_weight_weak_sum (x : WeakQuietExpansionCase plan prices)
    (v u : x.Vertex) :
    Real.sqrt (x.mass u / x.mass v) *
      (∑ γ : (x.c.stage x.i).fam.Γ v u, ∑ d ∈ Finset.Icc 2 x.order,
        weakQuietCoefficientWeight x v u γ d) ≤ x.b v u := by
  apply le_trans _ (weak_quiet_coefficient_weight_sum x v u)
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Finset.sum_le_sum
  intro γ _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans x.c.order_ge⟩
  · intro d _ _
    exact weak_quiet_coefficient_weight_nonneg x v u γ d

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Coarse
namespace AVRegularity.WeakEntryProofs

/-! Dimensionless prices for the genuine finite quiet margin paths. The scalar
smoothing price depends only on the request and the chosen finite path depth;
all physical length and diffusivity factors cancel against cube volume. -/

/-- An explicit uniform positive smoothing price on every gap of length at
least delta, retaining only the fixed upper order cap. -/
theorem weak_scalar_endpoint_price_le_uniform {ν ρ δ a b : ℝ}
    (hν : 0 < ν) (hδ : 0 < δ) (hlen : δ ≤ b - a) {P Q : ℕ} (hP : P ≤ Q) :
    weakScalarEndpointPrice ν ρ a b P ≤
      Real.sqrt (2 * (4 + 8 * ρ ^ 2 * (Q + 1) / (ν * δ)) ^ Q) := by
  have hden : 0 < ν * δ := mul_pos hν hδ
  have hab : 0 < b - a := hδ.trans_le hlen
  have hn : 0 ≤ 8 * ρ ^ 2 * (P + 1 : ℕ) := by positivity
  have hnum : 8 * ρ ^ 2 * (P + 1 : ℕ) ≤ 8 * ρ ^ 2 * (Q + 1 : ℕ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.succ_le_succ hP) (by positivity)
  have hfrac : 8 * ρ ^ 2 * (P + 1 : ℕ) / (ν * (b - a)) ≤
      8 * ρ ^ 2 * (Q + 1 : ℕ) / (ν * δ) :=
    (div_le_div_of_nonneg_left hn hden (mul_le_mul_of_nonneg_left hlen hν.le)).trans
      (div_le_div_of_nonneg_right hnum hden.le)
  have hbase : 1 ≤ 4 + 8 * ρ ^ 2 * (Q + 1 : ℕ) / (ν * δ) := by
    have hh : 0 ≤ 8 * ρ ^ 2 * (Q + 1 : ℕ) / (ν * δ) := by positivity
    linarith only [hh]
  push_cast at hfrac hbase
  unfold weakScalarEndpointPrice
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact (pow_le_pow_left₀ (by positivity) (by linarith only [hfrac]) P).trans
    (pow_le_pow_right₀ hbase hP)

namespace Assembly
variable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}

/-- The scalar price of one long gap after allocating n insertions. -/
def weakQuietLongGapPrice (x : WeakQuietExpansionCase plan prices) (n : ℕ) : ℝ :=
  2 * (4 + 16 * (plan.radius x.R) ^ 2 * (x.cap + 1 : ℕ) * (n + 1 : ℕ)) ^ x.cap

/-- The exact heat quiet margin length, with neither an order cap nor a data price. -/
theorem weak_quiet_heat_length (x : WeakQuietExpansionCase plan prices) :
    x.right - x.left = x.c.D.eps (x.i - 1) ^ 2 / x.c.D.κ x.c.M := by
  unfold WeakQuietExpansionCase.right WeakQuietExpansionCase.left
  ring

/-- The only physical scale identity needed in the midpoint smoothing price. -/
theorem weak_quiet_midpoint_price_scale (x : WeakQuietExpansionCase plan prices) (n : ℕ) :
    4 + 8 * x.radius ^ 2 * (x.cap + 1 : ℕ) /
      (x.c.D.κ x.c.M * (((x.right - x.left) / (n + 1 : ℕ)) / 2)) =
      4 + 16 * (plan.radius x.R) ^ 2 * (x.cap + 1 : ℕ) * (n + 1 : ℕ) := by
  rw [weak_quiet_heat_length]
  unfold WeakQuietExpansionCase.radius
  have heps := ne_of_gt x.bounds.1
  have hnu := ne_of_gt x.bounds.2.1
  have hn : (n + 1 : ℝ) ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < n + 1)
  push_cast
  field_simp [heps, hnu, hn]
  ring

/-- Every long gap has the same dimensionless midpoint price, uniformly in
all retained positive and negative orders. -/
theorem weak_quiet_long_gap_price_bound (x : WeakQuietExpansionCase plan prices) (n : ℕ) :
    WeakQuietGapPriceBound x ((x.right - x.left) / (n + 1 : ℕ)) (weakQuietLongGapPrice x n) := by
  intro P K hPK a b ha hab hb hlen
  have hδ : 0 < (x.right - x.left) / (n + 1 : ℕ) :=
    div_pos (sub_pos.mpr x.heat_window.1) (by positivity)
  have hhδ := half_pos hδ
  have hleft : ((x.right - x.left) / (n + 1 : ℕ)) / 2 ≤ (a + b) / 2 - a := by
    linarith only [hlen]
  have hright : ((x.right - x.left) / (n + 1 : ℕ)) / 2 ≤ b - (a + b) / 2 := by
    linarith only [hlen]
  have hP := weak_scalar_endpoint_price_le_uniform (ρ := x.radius) x.bounds.2.1 hhδ hleft (by omega : P ≤ x.cap)
  have hK := weak_scalar_endpoint_price_le_uniform (ρ := x.radius) x.bounds.2.1 hhδ hright (by omega : K ≤ x.cap)
  have hs := weak_quiet_midpoint_price_scale x n
  push_cast at hs hP hK
  rw [hs] at hP hK
  have hB : 0 ≤ 2 * (4 + 16 * (plan.radius x.R) ^ 2 * (x.cap + 1 : ℕ) * (n + 1 : ℕ)) ^ x.cap := by
    positivity
  push_cast at hB
  unfold weakQuietLongGapPrice
  push_cast
  exact (mul_le_mul hP hK (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq
    (Real.mul_self_sqrt hB)

/-- Products of actual insertion rates are the b-walk weight times a scalar
rate, with exactly one bounded scalar propagation for each insertion. -/
theorem weak_quiet_instant_cost_eq (x : WeakQuietExpansionCase plan prices)
    (n : ℕ) (v u : x.Vertex) (π : WeakQuietWalk x.Vertex n v u) :
    weakQuietInstantCost x n v u π =
      (Real.sqrt 2 * (x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice)) ^ n *
        weakQuietWalkWeight x.b n v u π := by
  induction n generalizing v with
  | zero => simp only [weakQuietInstantCost, weakQuietWalkWeight, pow_zero, one_mul]
  | succ n ih =>
    change (Σ w : x.Vertex, WeakQuietWalk x.Vertex n w u) at π
    simp only [weakQuietInstantCost, weakQuietInsertionRate, ih, weakQuietWalkWeight, pow_succ]
    ring

/-- Time-cube volume cancels every dimensional source rate. Only a
request-level insertion price remains. -/
theorem weak_quiet_instant_cost_volume (x : WeakQuietExpansionCase plan prices)
    (n : ℕ) (v u : x.Vertex) (π : WeakQuietWalk x.Vertex n v u) :
    weakQuietInstantCost x n v u π * (x.right - x.left) ^ n =
      (Real.sqrt 2 * x.insertionPrice) ^ n * weakQuietWalkWeight x.b n v u π := by
  have hscale : (Real.sqrt 2 *
      (x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice)) *
      (x.right - x.left) = Real.sqrt 2 * x.insertionPrice := by
    rw [weak_quiet_heat_length]
    field_simp [ne_of_gt x.bounds.1, ne_of_gt x.bounds.2.1]
  rw [weak_quiet_instant_cost_eq]
  calc
    _ = ((Real.sqrt 2 * (x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice)) *
        (x.right - x.left)) ^ n * weakQuietWalkWeight x.b n v u π := by
      rw [mul_pow (Real.sqrt 2 *
        (x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice)) (x.right - x.left) n]
      exact mul_right_comm _ _ _
    _ = _ := by rw [hscale]

/-- A pre-data dimensionless price for every retained scalar/source word. -/
def weakQuietScalarPathPrice (plan : WeakPassagePlan) (prices : WeakQuietPathPrices)
    {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (n : ℕ) : ℝ :=
  let r := 1 + A.Jw * A.Nw
  let cap := R.Kw + prices.depth R * r
  2 * (4 + 16 * (plan.radius R) ^ 2 * (cap + 1 : ℕ) * (n + 1 : ℕ)) ^ cap *
    (Real.sqrt 2 * (2 * (cap + 1 : ℕ) / plan.radius R) ^ r) ^ n

/-- The explicit numerical domination required of the chosen scalar prices. -/
def WeakQuietScalarPricesOK (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) : Prop :=
  ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) n,
    n ≤ prices.depth R → weakQuietScalarPathPrice plan prices R n ≤ prices.scalar R n

/-- Every actual b-walk has a nonnegative weight, including the empty path. -/
theorem weak_quiet_walk_weight_nonneg (x : WeakQuietExpansionCase plan prices)
    (n : ℕ) (v u : x.Vertex) (π : WeakQuietWalk x.Vertex n v u) :
    0 ≤ weakQuietWalkWeight x.b n v u π := by
  induction n generalizing v with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (x.bounds.2.2.2.2.1 v π.1) (ih π.1 π.2)

/-- **One step** with all PDE, signed-source word and Bochner integration
inputs discharged. Only the explicitly stated numerical plan conditions remain. -/
theorem weak_quiet_scalar_paths (hok : WeakQuietRowsPlanOK plan prices)
    (hprices : WeakQuietScalarPricesOK plan prices) : WeakQuietScalarPathStatement plan prices := by
  intro x S
  obtain ⟨hd⟩ := weak_quiet_parent_drift x.c
    ((hok.drift x.R x.c.j₀).trans x.c.level_ge) (hok.small x.R)
    x.i x.level_lt x.left x.right x.cap
  refine ⟨weakQuietBackwardEvolution x hd, weak_quiet_walk_integrable x hd S, ?_⟩
  intro n hn v u π
  let δ := (x.right - x.left) / (n + 1 : ℕ)
  have hδ : 0 < δ := div_pos (sub_pos.mpr x.heat_window.1) (by positivity)
  have hlen : (n + 1 : ℕ) * δ ≤ x.right - x.left := by
    dsimp only [δ]
    rw [mul_div_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < (n + 1 : ℕ)))]
  have hG : 0 ≤ weakQuietLongGapPrice x n := by unfold weakQuietLongGapPrice; positivity
  obtain ⟨Z, hZ, hp⟩ := weak_quiet_integrated_word_represented x S hd n x.R.Kw hn
    ((Nat.add_le_add_left (Nat.mul_le_mul_right x.order hn) x.R.Kw)) v u π
    hδ hG hlen (weak_quiet_long_gap_price_bound x n)
    (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value u x.left))
  refine ⟨Z, ?_, ?_⟩
  · intro φ
    exact hp (truncateTorusHk (x.path_reserve n hn) φ)
  · have hin : ‖truncateTorusHk (Nat.zero_le x.R.Kw) (x.value u x.left)‖ = x.inputSize u := by
      have hh := weak_quiet_input_size x u
      rw [CycleJointProofs.factorialNormSq_order_zero_measure, Real.sqrt_sq (norm_nonneg _)] at hh
      exact hh
    rw [hin] at hZ
    have hc : ((x.inputSize u * weakQuietLongGapPrice x n * weakQuietInstantCost x n v u π) *
        (x.right - x.left) ^ n) =
        weakQuietScalarPathPrice plan prices x.R n * weakQuietWalkWeight x.b n v u π * x.inputSize u := by
      calc
        _ = (weakQuietLongGapPrice x n *
            (weakQuietInstantCost x n v u π * (x.right - x.left) ^ n)) * x.inputSize u := by ring
        _ = _ := by
          rw [weak_quiet_instant_cost_volume]
          dsimp only [weakQuietScalarPathPrice, weakQuietLongGapPrice,
            WeakQuietExpansionCase.cap, WeakQuietExpansionCase.order, WeakQuietExpansionCase.insertionPrice]
          ring
    rw [hc] at hZ
    exact hZ.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hprices x.R n hn)
        (weak_quiet_walk_weight_nonneg x n v u π))
      (Real.sqrt_nonneg _))

/-- Choose the scalar prices explicitly before any level, ambient cap, or datum. -/
def weakQuietScalarPrices (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) :
    WeakQuietPathPrices :=
  { prices with
    scalar := weakQuietScalarPathPrice plan prices
    nonneg := by
      intro B A R n
      unfold weakQuietScalarPathPrice
      have hr := plan.radius_pos R
      positivity }

end Assembly

end AVRegularity.WeakEntryProofs
end
end
end
