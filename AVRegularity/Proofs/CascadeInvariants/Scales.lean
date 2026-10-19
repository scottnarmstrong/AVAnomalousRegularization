-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Construction.ScheduleFloor
import AVRegularity.CycleWords.WeightedRawProductAlgebra
import AVRegularity.CycleReference.TorusChartEquation
import AVRegularity.Construction.Scales.Times
import AVRegularity.Definitions.Finite.FiniteLiftBridge
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVRegularity.Construction.Stream.NextAdmissible

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the cutoff weights of the odd slots are a partition of unity.** The weights
`ϖ_{m,k}(t) = ψ(5/2 - 2|t - kτ_m|/τ_m)` lie in `[0,1]` and vanish for `|t - kτ_m| ≥ 5τ_m/4`; at
every time at most the two odd slots `k₀ ≤ t/τ_m < k₀ + 2` are active, and their weights add up to
one because `ψ(x) + ψ(1 - x) = 1`. Hence every finite sum of the weights of odd slots is at most
one (`sum_ocCutoff_le_one`), and a sum `Σ_k ϖ_k(t) Y_k` is a sub-convex combination
(`sum_ocCutoff_mul_le`): the transferred constituent is, at each time, a convex combination of the
terms of the finer slots. -/

theorem smoothTransition_add_one_sub (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  unfold Real.smoothTransition
  rw [sub_sub_cancel, add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x), ← add_div,
    div_self (Real.smoothTransition.pos_denom x).ne']

variable {α q : ℝ} {Λ m : ℕ}

theorem ocCutoff_nonneg (k : ℤ) (t : ℝ) : 0 ≤ ocCutoff α q Λ m k t :=
  Real.smoothTransition.nonneg _

theorem ocCutoff_eq_zero_of_far (hτ : 0 < ocTau α q Λ m) (k : ℤ) (t : ℝ)
    (h : 5 / 4 * ocTau α q Λ m ≤ |t - (k : ℝ) * ocTau α q Λ m|) : ocCutoff α q Λ m k t = 0 := by
  unfold ocCutoff
  apply Real.smoothTransition.zero_of_nonpos
  have : 5 / 2 ≤ 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m := by
    rw [le_div_iff₀ hτ]
    linarith
  linarith

/-- **The active pair of odd slots**: at every time all odd slots but two consecutive ones have
weight zero, and the weights of these two add up to one. -/
theorem ocCutoff_active_pair (hτ : 0 < ocTau α q Λ m) (t : ℝ) :
    ∃ k₀ : ℤ, Odd k₀ ∧ (∀ k : ℤ, Odd k → k ≠ k₀ → k ≠ k₀ + 2 → ocCutoff α q Λ m k t = 0) ∧
      ocCutoff α q Λ m k₀ t + ocCutoff α q Λ m (k₀ + 2) t = 1 := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u * ocTau α q Λ m := ⟨t / ocTau α q Λ m, (div_mul_cancel₀ t hτ.ne').symm⟩
  obtain ⟨k₀, hk₀odd, hk₀le, hk₀lt⟩ : ∃ k₀ : ℤ, Odd k₀ ∧ (k₀ : ℝ) ≤ u ∧ u < k₀ + 2 := by
    refine ⟨2 * ⌊(u + 1) / 2⌋ - 1, ⟨⌊(u + 1) / 2⌋ - 1, by ring⟩, ?_, ?_⟩
    · have := Int.floor_le ((u + 1) / 2)
      push_cast
      linarith
    · have := Int.lt_floor_add_one ((u + 1) / 2)
      push_cast
      linarith
  refine ⟨k₀, hk₀odd, fun k hk h1 h2 => ?_, ?_⟩
  · apply ocCutoff_eq_zero_of_far hτ
    obtain ⟨j, rfl⟩ := hk
    obtain ⟨j₀, rfl⟩ := hk₀odd
    have hcase : j ≤ j₀ - 1 ∨ j₀ + 2 ≤ j := by omega
    rcases hcase with h | h
    · have hj : (j : ℝ) ≤ j₀ - 1 := by exact_mod_cast h
      push_cast at hk₀le ⊢
      have : 2 * ocTau α q Λ m ≤ u * ocTau α q Λ m - (2 * j + 1) * ocTau α q Λ m := by
        rw [← sub_mul]
        exact mul_le_mul_of_nonneg_right (by linarith) hτ.le
      exact (by linarith : 5 / 4 * ocTau α q Λ m ≤ 2 * ocTau α q Λ m).trans
        (this.trans (le_abs_self _))
    · have hj : (j₀ : ℝ) + 2 ≤ j := by exact_mod_cast h
      push_cast at hk₀lt ⊢
      have : 2 * ocTau α q Λ m ≤ (2 * j + 1) * ocTau α q Λ m - u * ocTau α q Λ m := by
        rw [← sub_mul]
        exact mul_le_mul_of_nonneg_right (by linarith) hτ.le
      rw [abs_sub_comm]
      exact (by linarith : 5 / 4 * ocTau α q Λ m ≤ 2 * ocTau α q Λ m).trans
        (this.trans (le_abs_self _))
  · unfold ocCutoff
    have hτ0 : ocTau α q Λ m ≠ 0 := hτ.ne'
    have h1 : 2 * |u * ocTau α q Λ m - (k₀ : ℝ) * ocTau α q Λ m| / ocTau α q Λ m =
        2 * (u - k₀) := by
      rw [← sub_mul, abs_of_nonneg (mul_nonneg (sub_nonneg.2 hk₀le) hτ.le), mul_div_assoc,
        mul_div_cancel_right₀ _ hτ0]
    have h2 : 2 * |u * ocTau α q Λ m - ((k₀ + 2 : ℤ) : ℝ) * ocTau α q Λ m| / ocTau α q Λ m =
        2 * (k₀ + 2 - u) := by
      have hneg : -((u - ((k₀ + 2 : ℤ) : ℝ)) * ocTau α q Λ m) =
          ((k₀ : ℝ) + 2 - u) * ocTau α q Λ m := by
        push_cast
        ring
      rw [← sub_mul, abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by push_cast; linarith)
        hτ.le), hneg, mul_div_assoc, mul_div_cancel_right₀ _ hτ0]
    rw [h1, h2]
    have : 5 / 2 - 2 * ((k₀ : ℝ) + 2 - u) = 1 - (5 / 2 - 2 * (u - k₀)) := by ring
    rw [this, smoothTransition_add_one_sub]

/-- **The weights of the odd slots add up to at most one.** -/
theorem sum_ocCutoff_le_one (hτ : 0 < ocTau α q Λ m) (S : Finset ℤ) (hS : ∀ k ∈ S, Odd k)
    (t : ℝ) : ∑ k ∈ S, ocCutoff α q Λ m k t ≤ 1 := by
  obtain ⟨k₀, -, hfar, hpair⟩ := ocCutoff_active_pair hτ t
  have hne : k₀ ≠ k₀ + 2 := by omega
  calc ∑ k ∈ S, ocCutoff α q Λ m k t
      ≤ ∑ k ∈ S ∪ {k₀, k₀ + 2}, ocCutoff α q Λ m k t :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          fun _ _ _ => ocCutoff_nonneg _ _
    _ = ∑ k ∈ ({k₀, k₀ + 2} : Finset ℤ), ocCutoff α q Λ m k t := by
        refine (Finset.sum_subset Finset.subset_union_right fun k hk hk' => ?_).symm
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
        have hkS : k ∈ S := by
          rcases Finset.mem_union.mp hk with h | h
          · exact h
          · simp only [Finset.mem_insert, Finset.mem_singleton] at h
            exact absurd h (by tauto)
        exact hfar k (hS k hkS) hk'.1 hk'.2
    _ = 1 := by rw [Finset.sum_pair hne, hpair]

/-- **The weights of the odd slots add up to one** over any set containing the active slots. -/
theorem sum_ocCutoff_eq_one (hτ : 0 < ocTau α q Λ m) (S : Finset ℤ) (hS : ∀ k ∈ S, Odd k)
    (t : ℝ) (hact : ∀ k : ℤ, Odd k → ocCutoff α q Λ m k t ≠ 0 → k ∈ S) :
    ∑ k ∈ S, ocCutoff α q Λ m k t = 1 := by
  obtain ⟨k₀, hk₀, hfar, hpair⟩ := ocCutoff_active_pair hτ t
  have hne : k₀ ≠ k₀ + 2 := by omega
  have hk₂ : Odd (k₀ + 2) := hk₀.add_even even_two
  calc ∑ k ∈ S, ocCutoff α q Λ m k t
      = ∑ k ∈ S ∪ {k₀, k₀ + 2}, ocCutoff α q Λ m k t := by
        refine Finset.sum_subset Finset.subset_union_left fun k hk hkS => ?_
        by_contra h0
        rcases Finset.mem_union.mp hk with h | h
        · exact hkS h
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl
          · exact hkS (hact _ hk₀ h0)
          · exact hkS (hact _ hk₂ h0)
    _ = ∑ k ∈ ({k₀, k₀ + 2} : Finset ℤ), ocCutoff α q Λ m k t := by
        refine (Finset.sum_subset Finset.subset_union_right fun k hk hk' => ?_).symm
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
        have hkS : k ∈ S := by
          rcases Finset.mem_union.mp hk with h | h
          · exact h
          · simp only [Finset.mem_insert, Finset.mem_singleton] at h
            exact absurd h (by tauto)
        exact hfar k (hS k hkS) hk'.1 hk'.2
    _ = 1 := by rw [Finset.sum_pair hne, hpair]

/-- **A sum weighted by the odd-slot cutoffs is a sub-convex combination.** -/
theorem sum_ocCutoff_mul_le (hτ : 0 < ocTau α q Λ m) (S : Finset ℤ) (hS : ∀ k ∈ S, Odd k)
    (t : ℝ) (Y : ℤ → ℝ≥0∞) {Ybar : ℝ≥0∞} (hY : ∀ k ∈ S, Y k ≤ Ybar) :
    ∑ k ∈ S, ENNReal.ofReal (ocCutoff α q Λ m k t) * Y k ≤ Ybar := by
  calc ∑ k ∈ S, ENNReal.ofReal (ocCutoff α q Λ m k t) * Y k
      ≤ ∑ k ∈ S, ENNReal.ofReal (ocCutoff α q Λ m k t) * Ybar :=
        Finset.sum_le_sum fun k hk => mul_le_mul_right (hY k hk) _
    _ = ENNReal.ofReal (∑ k ∈ S, ocCutoff α q Λ m k t) * Ybar := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun k _ => ocCutoff_nonneg k t]
    _ ≤ 1 * Ybar := by
        refine mul_le_mul_left ?_ _
        exact ENNReal.ofReal_le_one.mpr (sum_ocCutoff_le_one hτ S hS t)
    _ = Ybar := one_mul _

end AVRegularity.Providers.CascadeInvariants
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: invariants of the cascade.** Along the cascade from a seed:
* every stage has the tags of its provenance (`hasTags_of_cascade`), since restrictions keep them
  (`hasTags_restrict`) and every actual successor has them;
* a higher identity (`birthExcess ≥ 1`) has length at most the wavelength of its level
  (`length_le_eps_of_cascade`): a direct transport keeps the length of its old identity (and the
  wavelengths grow towards the coarse levels), a letter born at the passage `m → m-1` has the fresh
  length `R_{m-1} ≤ ε_{m-1}`, and a quadratic conversion has `birthExcess = 0`. This is the
  source's "a higher source keeps its original length through every passage" with
  `ρ_b ≤ ρ_i ≤ E`. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem hasTags_restrict {P : ProvParams} {G : GenStage D hr Dm b j₀} (hG : G.HasTags P)
    (S : Finset Comp) (hS : S ⊆ G.comps) : (G.restrict S hS).HasTags P :=
  fun v u γ => hG ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩ γ

/-- **Every stage of the cascade has the tags of its provenance.** -/
theorem hasTags_of_cascade {P : ProvParams} {Mn : SuccMenu} {seed G : GenStage D hr Dm b j₀}
    (hseed : seed.HasTags P) (hG : IsCascadeStage D P Mn seed G) : G.HasTags P := by
  induction hG with
  | seed => exact hseed
  | step _ hsucc _ => exact hasTags_restrict hsucc.2.2.2.2.1 _ _

/-- The levels of the cascade decrease from the seed. -/
theorem level_le_of_cascade {P : ProvParams} {Mn : SuccMenu} {seed G : GenStage D hr Dm b j₀}
    (hG : IsCascadeStage D P Mn seed G) : G.level ≤ seed.level := by
  induction hG with
  | seed => exact le_rfl
  | @step G G' _ hsucc ih =>
    show G'.level ≤ seed.level
    rw [hsucc.2.1]
    omega

theorem Prov.tags_dir (P : ProvParams) (m : ℕ) (src : Prov) :
    (Prov.tags P (.dir m src)).length = (src.tags P).length ∧
      (Prov.tags P (.dir m src)).birthExcess = (src.tags P).birthExcess := by
  simp [Prov.tags]

theorem Prov.tags_quad_birthExcess (P : ProvParams) (m : ℕ) (path : List (Comp × Comp × Prov)) :
    (Prov.tags P (.quad m path)).birthExcess = 0 := by
  simp only [Prov.tags]
  split <;> rfl

theorem Prov.tags_letter_length (P : ProvParams) (m : ℕ) (l : WordLetter)
    (path : List (Comp × Comp × Prov)) : (Prov.tags P (.letter m l path)).length = P.Rb (m - 1) := by
  simp [Prov.tags]

/-- **The lengths of the higher identities of the cascade** are at most the wavelengths of their
levels, given the seed lengths, the decrease of the wavelengths towards the fine levels and the
fresh lengths `R_b ≤ ε_b` at the birth levels `m₀ ≤ b < n` of the passages below the seed
level `n`. -/
theorem length_le_eps_of_cascade {P : ProvParams} {Mn : SuccMenu} {seed : GenStage D hr Dm b j₀}
    (hseedT : seed.HasTags P)
    (hseedL : ∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level)
    (hanti : ∀ k, D.eps (k + 1) ≤ D.eps k) {m₀ : ℕ}
    (hRb : ∀ b', m₀ ≤ b' → b' < seed.level → P.Rb b' ≤ D.eps b')
    {G : GenStage D hr Dm b j₀} (hG : IsCascadeStage D P Mn seed G) :
    m₀ ≤ G.level → ∀ v u (γ : G.fam.Γ v u), 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ D.eps G.level := by
  induction hG with
  | seed => exact fun _ => hseedL
  | @step G G' hc hsucc ih =>
    intro hlev v u γ hbe
    obtain ⟨hl1, hlev', -, -, htags, -, e, Cc, Cc0, -, -, hall⟩ := hsucc
    have hGT : G.HasTags P := hasTags_of_cascade hseedT hc
    have hGs : G.level ≤ seed.level := level_le_of_cascade hc
    have hlevR : G'.level = G.level - 1 := hlev'
    have hlevm : m₀ ≤ G'.level := hlev
    have key : ∀ (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u'),
        1 ≤ (G'.fam.identity v' u' γ').record.birthExcess →
        (G'.fam.identity v' u' γ').record.length ≤ D.eps G'.level := by
      intro v' u' γ' hbe'
      obtain ⟨hT, -⟩ := htags v' u' γ'
      obtain ⟨hprov, -⟩ := hall v' u' γ'
      rw [hT.2.2.1, hprov] at hbe'
      rw [hT.2.2.2.1, hprov]
      generalize (e v' u' γ').1 = s at hbe' ⊢
      cases s with
      | copyDir t v₀ u₀ γ₀ =>
        simp only [SuccSource.prov] at hbe' ⊢
        rw [(Prov.tags_dir P _ _).1]
        rw [(Prov.tags_dir P _ _).2] at hbe'
        obtain ⟨hT₀, -⟩ := hGT v₀ u₀ γ₀
        rw [← hT₀.2.2.1] at hbe'
        rw [← hT₀.2.2.2.1]
        have h1 := ih (by omega) v₀ u₀ γ₀ hbe'
        have h2 : D.eps G.level ≤ D.eps G'.level := by
          rw [hlevR]
          have := hanti (G.level - 1)
          rwa [Nat.sub_add_cancel hl1] at this
        exact h1.trans h2
      | copyQuad t h π =>
        simp only [SuccSource.prov, Prov.tags_quad_birthExcess] at hbe'
        omega
      | letterDiag t u₀ =>
        simp only [SuccSource.prov, Prov.tags_letter_length]
        rw [hlevR]
        exact hRb _ (by omega) (by omega)
      | letterMean t n h π =>
        simp only [SuccSource.prov, Prov.tags_letter_length]
        rw [hlevR]
        exact hRb _ (by omega) (by omega)
      | letterCov t n h a a' π =>
        simp only [SuccSource.prov, Prov.tags_letter_length]
        rw [hlevR]
        exact hRb _ (by omega) (by omega)
    exact key ⟨v.1, Finset.filter_subset _ _ v.2⟩ ⟨u.1, Finset.filter_subset _ _ u.2⟩ γ hbe

/-! ### Grades along the edges -/

theorem compGrade_succComp_nil (m : ℕ) (c : Comp) :
    compGrade (succComp m c []) = compGrade c := by
  simp [succComp]

theorem compGrade_succComp_ne (m : ℕ) (c : Comp) {t : List WordLetter} (ht : t ≠ []) :
    compGrade (succComp m c t) = compGrade c + 1 := by
  simp [succComp, compGrade, ht]

theorem compGrade_succComp_mono (m : ℕ) {c c' : Comp} (h : compGrade c ≤ compGrade c')
    (t : List WordLetter) : compGrade (succComp m c t) ≤ compGrade (succComp m c' t) := by
  by_cases ht : t = []
  · subst ht
    rw [compGrade_succComp_nil, compGrade_succComp_nil]
    exact h
  · rw [compGrade_succComp_ne m c ht, compGrade_succComp_ne m c' ht]
    omega

theorem compGrade_succComp_le_append (m : ℕ) {c c' : Comp} (h : compGrade c ≤ compGrade c')
    (t : List WordLetter) (l : WordLetter) :
    compGrade (succComp m c t) ≤ compGrade (succComp m c' (t ++ [l])) := by
  rw [compGrade_succComp_ne m c' (by simp)]
  by_cases ht : t = []
  · subst ht
    rw [compGrade_succComp_nil]
    omega
  · rw [compGrade_succComp_ne m c ht]
    omega

/-- Along a path whose edges do not lower the grade, the grades of the targets of the steps do
not decrease. -/
theorem stagePath_grade_mono {G : GenStage D hr Dm b j₀}
    (hG : ∀ (v u : CompIn G.comps), Nonempty (G.fam.Γ v u) → compGrade u.1 ≤ compGrade v.1)
    {h : ℕ} (π : StagePath G h) :
    ∀ (i j : ℕ) (hi : i < h) (hj : j < h), i ≤ j →
      compGrade (π.step ⟨i, hi⟩).1.1 ≤ compGrade (π.step ⟨j, hj⟩).1.1 := by
  intro i j hi hj hij
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact le_rfl
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have h1 := ih (by omega) (by omega)
      have h2 := hG (π.step ⟨j + 1, hj⟩).1 (π.step ⟨j + 1, hj⟩).2.1 ⟨(π.step ⟨j + 1, hj⟩).2.2⟩
      rw [π.joined j hj] at h2
      exact h1.trans h2
    · obtain rfl : i = j + 1 := by omega
      exact le_rfl

/-- The source of a path has at most the grade of its target. -/
theorem stagePath_grade_src_le_tgt {G : GenStage D hr Dm b j₀}
    (hG : ∀ (v u : CompIn G.comps), Nonempty (G.fam.Γ v u) → compGrade u.1 ≤ compGrade v.1)
    {h : ℕ} (π : StagePath G h) (hh : 1 ≤ h) : compGrade π.src ≤ compGrade π.tgt := by
  have h0 : 0 < h := hh
  have h1 := hG (π.step ⟨0, h0⟩).1 (π.step ⟨0, h0⟩).2.1 ⟨(π.step ⟨0, h0⟩).2.2⟩
  have h2 := stagePath_grade_mono hG π 0 (h - 1) h0 (by omega) (Nat.zero_le _)
  simp only [StagePath.src, StagePath.tgt, h0, ↓reduceDIte]
  exact h1.trans h2

/-- The target of every step of a path has at most the grade of the target of the path. -/
theorem stagePath_grade_step_le_tgt {G : GenStage D hr Dm b j₀}
    (hG : ∀ (v u : CompIn G.comps), Nonempty (G.fam.Γ v u) → compGrade u.1 ≤ compGrade v.1)
    {h : ℕ} (π : StagePath G h) (j : Fin h) : compGrade (π.step j).1.1 ≤ compGrade π.tgt := by
  have h0 : 0 < h := lt_of_le_of_lt (Nat.zero_le _) j.2
  have h2 := stagePath_grade_mono hG π j.1 (h - 1) j.2 (by omega) (by omega)
  simp only [StagePath.tgt, h0, ↓reduceDIte]
  exact h2

/-- The source component of a source has at most the grade of its target component. -/
theorem succSource_grade_src_le_tgt {G : GenStage D hr Dm b j₀}
    (hG : ∀ (v u : CompIn G.comps), Nonempty (G.fam.Γ v u) → compGrade u.1 ≤ compGrade v.1)
    {A : Finset WordLetter} {J : ℕ} (s : SuccSource G) (hs : s.Valid A J) (m : ℕ) :
    compGrade (s.srcComp m) ≤ compGrade (s.tgtComp m) := by
  cases s with
  | copyDir t v u γ => exact compGrade_succComp_mono m (hG v u ⟨γ⟩) t
  | copyQuad t h π => exact compGrade_succComp_mono m (stagePath_grade_src_le_tgt hG π hs.2.2) t
  | letterDiag t u => exact compGrade_succComp_le_append m le_rfl t _
  | letterMean t n h π =>
    exact compGrade_succComp_le_append m (stagePath_grade_src_le_tgt hG π hs.2.2) t _
  | letterCov t n h a a' π =>
    exact compGrade_succComp_le_append m (stagePath_grade_src_le_tgt hG π hs.2.2) t _

/-- **Along the cascade the edges do not lower the grade**: the source component of every
identity has at most the grade of its target component (the seed components have no births; a
copy keeps the word of both ends, a letter edge appends its letter to the target). -/
theorem grade_mono_of_cascade {P : ProvParams} {Mn : SuccMenu} {seed : GenStage D hr Dm b j₀}
    (hseedB : ∀ v : CompIn seed.comps, v.1.births = []) {G : GenStage D hr Dm b j₀}
    (hG : IsCascadeStage D P Mn seed G) :
    ∀ (v u : CompIn G.comps), Nonempty (G.fam.Γ v u) → compGrade u.1 ≤ compGrade v.1 := by
  induction hG with
  | seed =>
    intro v u _
    simp [compGrade, hseedB u, hseedB v]
  | @step G G' hc hsucc ih =>
    intro v u hγ
    obtain ⟨γ⟩ := hγ
    obtain ⟨-, -, -, -, -, -, e, -, -, -, -, -⟩ := hsucc
    have hs := (e ⟨v.1, Finset.filter_subset _ _ v.2⟩ ⟨u.1, Finset.filter_subset _ _ u.2⟩ γ).2
    have := succSource_grade_src_le_tgt ih _ hs.1 G.level
    rw [hs.2.1, hs.2.2] at this
    exact this

section Seed

variable [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]

/-- A generated seed has the tags of its provenance. -/
theorem hasTags_of_generatedSeed {law : BirthLaw} {P : ProvParams} {seedK freshK : ℕ → KernelSpec}
    {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {M : ℕ} {kS : InvConsts}
    {seed : GenStage D hr Dm b j₀} {n : ℕ} {tS tf Ce τe : ℝ} {r₀ D₀ : ℕ}
    (h : IsGeneratedSeed law P seedK freshK φ₀ hφ₀ M kS seed n tS tf Ce τe r₀ D₀) :
    seed.HasTags P :=
  h.2.2.2.2.2.2.2.1.2.1

/-- The higher identities of a generated seed have lengths at most its wavelength. -/
theorem length_of_generatedSeed {law : BirthLaw} {P : ProvParams} {seedK freshK : ℕ → KernelSpec}
    {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {M : ℕ} {kS : InvConsts}
    {seed : GenStage D hr Dm b j₀} {n : ℕ} {tS tf Ce τe : ℝ} {r₀ D₀ : ℕ}
    (h : IsGeneratedSeed law P seedK freshK φ₀ hφ₀ M kS seed n tS tf Ce τe r₀ D₀) :
    ∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level := fun v u γ hbe => by
  have hlen := (h.2.2.2.2.2.1 v u γ).2.2 hbe
  rwa [← h.1] at hlen

end Seed
end

/-! **Ledger: the tags of the new identities.** From `G'.HasTags P`, `G.HasTags P` and the
provenance `G'.prov = s.prov m` of an actual successor, the record of a new identity in terms of
the records of the old identities of its source:
* a direct transport keeps the maximal order and the length and has the size `C · size`
  (`record_of_dir`);
* a quadratic conversion of a path has the maximal order `2` and the size `C · ∏_j size_j`
  (`record_of_quad`);
* a letter along a path has its present order, the fresh length `R_{m-1}` and the size
  `w_{m-1} C ε_{m-1}^{δ-η₀} · ∏_j size_j` (`record_of_letter`). -/

section
theorem pathTags_eq_map (P : ProvParams) (l : List (Comp × Comp × Prov)) :
    Prov.pathTags P l = l.map fun x => x.2.2.tags P := by
  induction l with
  | nil => simp [Prov.pathTags]
  | cons x rest ih =>
    obtain ⟨a, c, y⟩ := x
    simp [Prov.pathTags, ih]

theorem widestTags_eq_none {l : List ProvTags} (h : widestTags l = none) : l = [] := by
  by_contra hl
  have := widestTags_isSome hl
  rw [h] at this
  exact absurd this (by simp)

theorem Prov.tags_quad_order (P : ProvParams) (m : ℕ) (path : List (Comp × Comp × Prov)) :
    (Prov.tags P (.quad m path)).order = 2 := by
  simp only [Prov.tags]
  split <;> rfl

theorem Prov.tags_quad_witness (P : ProvParams) (m : ℕ) (path : List (Comp × Comp × Prov)) :
    (Prov.tags P (.quad m path)).witness =
      P.C * ((Prov.pathTags P path).map ProvTags.witness).prod := by
  simp only [Prov.tags]
  split
  · next h =>
    rw [widestTags_eq_none h]
    simp
  · rfl

theorem Prov.tags_letter (P : ProvParams) (m : ℕ) (l : WordLetter)
    (path : List (Comp × Comp × Prov)) :
    (Prov.tags P (.letter m l path)).order = letterOrder P.N P.p l ∧
      (Prov.tags P (.letter m l path)).length = P.Rb (m - 1) ∧
      (Prov.tags P (.letter m l path)).witness =
        P.w (m - 1) * P.C * P.eps (m - 1) ^ (P.δ - P.η0) *
          ((Prov.pathTags P path).map ProvTags.witness).prod := by
  simp [Prov.tags]

theorem Prov.tags_dir_all (P : ProvParams) (m : ℕ) (src : Prov) :
    (Prov.tags P (.dir m src)).order = (src.tags P).order ∧
      (Prov.tags P (.dir m src)).length = (src.tags P).length ∧
      (Prov.tags P (.dir m src)).witness = P.C * (src.tags P).witness := by
  simp [Prov.tags]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The product of the witnesses of the identities of a path is the product of their record
sizes. -/
theorem prod_witness_provList {P : ProvParams} {G : GenStage D hr Dm b j₀} (hG : G.HasTags P)
    {h : ℕ} (π : StagePath G h) :
    ((Prov.pathTags P π.provList).map ProvTags.witness).prod =
      ∏ j : Fin h, (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size := by
  rw [pathTags_eq_map]
  unfold StagePath.provList
  rw [List.map_ofFn, List.map_ofFn, List.prod_ofFn]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact ((hG (π.step j).1 (π.step j).2.1 (π.step j).2.2).1.1).symm

/-- **The record of a direct transport.** -/
theorem record_of_dir {P : ProvParams} {G G' : GenStage D hr Dm b j₀} (hG : G.HasTags P)
    (hG' : G'.HasTags P) {v u : CompIn G.comps} (γ : G.fam.Γ v u) {v' u' : CompIn G'.comps}
    (γ' : G'.fam.Γ v' u') {m : ℕ} (hprov : G'.prov v' u' γ' = .dir m (G.prov v u γ)) :
    (G'.fam.identity v' u' γ').maxOrder = (G.fam.identity v u γ).maxOrder ∧
      (G'.fam.identity v' u' γ').record.length = (G.fam.identity v u γ).record.length ∧
      (G'.fam.identity v' u' γ').record.size = P.C * (G.fam.identity v u γ).record.size := by
  obtain ⟨hm', ho'⟩ := hG' v' u' γ'
  obtain ⟨hm, ho⟩ := hG v u γ
  rw [hprov] at hm' ho'
  obtain ⟨h1, h2, h3⟩ := Prov.tags_dir_all P m (G.prov v u γ)
  exact ⟨by rw [ho', h1, ho], by rw [hm'.2.2.2.1, h2, hm.2.2.2.1],
    by rw [hm'.1, h3, hm.1]⟩

/-- **The record of a quadratic conversion.** -/
theorem record_of_quad {P : ProvParams} {G G' : GenStage D hr Dm b j₀} (hG : G.HasTags P)
    (hG' : G'.HasTags P) {h : ℕ} (π : StagePath G h) {v' u' : CompIn G'.comps}
    (γ' : G'.fam.Γ v' u') {m : ℕ} (hprov : G'.prov v' u' γ' = .quad m π.provList) :
    (G'.fam.identity v' u' γ').maxOrder = 2 ∧
      (G'.fam.identity v' u' γ').record.size = P.C *
        ∏ j : Fin h, (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size := by
  obtain ⟨hm', ho'⟩ := hG' v' u' γ'
  rw [hprov] at hm' ho'
  exact ⟨by rw [ho', Prov.tags_quad_order], by
    rw [hm'.1, Prov.tags_quad_witness, prod_witness_provList hG]⟩

/-- **The record of a letter along a path.** -/
theorem record_of_letter {P : ProvParams} {G G' : GenStage D hr Dm b j₀} (hG : G.HasTags P)
    (hG' : G'.HasTags P) {h : ℕ} (π : StagePath G h) {v' u' : CompIn G'.comps}
    (γ' : G'.fam.Γ v' u') {m : ℕ} (l : WordLetter)
    (hprov : G'.prov v' u' γ' = .letter m l π.provList) :
    (G'.fam.identity v' u' γ').maxOrder = letterOrder P.N P.p l ∧
      (G'.fam.identity v' u' γ').record.length = P.Rb (m - 1) ∧
      (G'.fam.identity v' u' γ').record.size =
        P.w (m - 1) * P.C * P.eps (m - 1) ^ (P.δ - P.η0) *
          ∏ j : Fin h, (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size := by
  obtain ⟨hm', ho'⟩ := hG' v' u' γ'
  rw [hprov] at hm' ho'
  obtain ⟨h1, h2, h3⟩ := Prov.tags_letter P m l π.provList
  exact ⟨by rw [ho', h1], by rw [hm'.2.2.2.1, h2], by
    rw [hm'.1, h3, prod_witness_provList hG]⟩
end

end AVRegularity.Providers.CascadeInvariants
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Providers.CascadeInvariants

/-! **The depth of the stages of the cascade**. Along the cascade
from a seed of depth `r₀` whose components have no births, every stage has depth at most
`r_H = succSchedR r₀ J H` (`cascade_depth`), hence every path of a stage has at most `r_H` edges
(`stagePath_length_le`). This is the depth schedule `r_g = (J+2)(r_{g-1}+1) - 1` of the
construction:
a component of grade `g` carries a rank at most `r_g`, strictly increasing
along the edges.
* The seed has the rank of its finite acyclic graph (`familyDepthRank`).
* At the passage `m → m-1` the component `(v, 𝔱)` has the rank
  `|𝔱| (r_{g(v)} + 1) + rank(v)` (`succRank`): a copy keeps the word and moves along at least one
  old edge, a letter edge appends one letter and moves along an old path (of no edge for the first
  source `𝖣`); the grades do not decrease along old edges (`grade_mono_of_cascade`), and a word has
  at most `J + 1` letters, so the rank of a new component of grade `g + 1` is at most
  `(J+1)(r_g+1) + r_g = r_{g+1}`.
* The decoding `(v, 𝔱)` of a component of the extended family is unambiguous because the births
  of the components of a stage of level `m` have scales at least `m` (the seed has none, the
  passage `m → m-1` adds the scale `m-1`). -/

/-- **A bounded rank, strictly increasing along the edges, bounds the depth.** -/
theorem hasDepthAtMost_of_rank {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h D P Ctx) {H : ℕ} (ρ : ι → ℕ) (hρ : ∀ v, ρ v ≤ H)
    (hs : ∀ v u, Nonempty (F.Γ v u) → ρ u < ρ v) : F.HasDepthAtMost H := by
  intro p
  by_contra hne
  have hne' : ∀ k : Fin (H + 1), Nonempty (F.Γ (p k.succ) (p k.castSucc)) := fun k => by
    by_contra hk
    exact hne ⟨k, not_nonempty_iff.mp hk⟩
  have hk : ∀ k : ℕ, ∀ hk : k < H + 2, k ≤ ρ (p ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h3 : ρ (p ⟨k, by omega⟩) < ρ (p ⟨k + 1, hk⟩) := hs _ _ (hne' ⟨k, by omega⟩)
      omega
  have h1 := hk (H + 1) (by omega)
  have h2 := hρ (p ⟨H + 1, by omega⟩)
  omega

/-! ### The depth schedule -/

theorem succSchedR_le_succ (r₀ J g : ℕ) : succSchedR r₀ J g ≤ succSchedR r₀ J (g + 1) := by
  show _ ≤ (J + 2) * (succSchedR r₀ J g + 1) - 1
  have h1 : 2 * (succSchedR r₀ J g + 1) ≤ (J + 2) * (succSchedR r₀ J g + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem succSchedR_mono (r₀ J : ℕ) : Monotone (succSchedR r₀ J) :=
  monotone_nat_of_le_succ (succSchedR_le_succ r₀ J)

/-- A word of at most `J + 1` letters over a rank at most `r_g` has rank at most `r_{g+1}`. -/
theorem succRank_bound {r₀ J g L a : ℕ} (hL : L ≤ J + 1) (ha : a ≤ succSchedR r₀ J g) :
    L * (succSchedR r₀ J g + 1) + a ≤ succSchedR r₀ J (g + 1) := by
  show _ ≤ (J + 2) * (succSchedR r₀ J g + 1) - 1
  have h1 : L * (succSchedR r₀ J g + 1) ≤ (J + 1) * (succSchedR r₀ J g + 1) :=
    Nat.mul_le_mul_right _ hL
  have h2 : (J + 2) * (succSchedR r₀ J g + 1) =
      (J + 1) * (succSchedR r₀ J g + 1) + (succSchedR r₀ J g + 1) := by ring
  omega

/-- The rank increases along an edge of the extended family. -/
theorem succRank_lt {r₀ J g g' L L' a a' : ℕ} (hg : g ≤ g') (hL : L ≤ L') (ha : a ≤ a')
    (hstrict : a < a' ∨ L < L') :
    L * (succSchedR r₀ J g + 1) + a < L' * (succSchedR r₀ J g' + 1) + a' := by
  have hr : succSchedR r₀ J g + 1 ≤ succSchedR r₀ J g' + 1 :=
    Nat.succ_le_succ (AVRegularity.Providers.CascadeInvariants.succSchedR_mono r₀ J hg)
  have h1 : L * (succSchedR r₀ J g + 1) ≤ L * (succSchedR r₀ J g' + 1) :=
    Nat.mul_le_mul_left _ hr
  rcases hstrict with h | h
  · have h2 : L * (succSchedR r₀ J g' + 1) ≤ L' * (succSchedR r₀ J g' + 1) :=
      Nat.mul_le_mul_right _ hL
    omega
  · have h2 : (L + 1) * (succSchedR r₀ J g' + 1) ≤ L' * (succSchedR r₀ J g' + 1) :=
      Nat.mul_le_mul_right _ h
    have h3 : (L + 1) * (succSchedR r₀ J g' + 1) =
        L * (succSchedR r₀ J g' + 1) + (succSchedR r₀ J g' + 1) := by ring
    omega

/-! ### The rank of the extended family -/

/-- The rank of a component of the extended family of the passage `m → m-1`, from the rank `ρ` of
the old stage: `|𝔱| (r_{g(v)} + 1) + ρ(v)` on `(v, 𝔱)`. -/
def succRank (r₀ J m : ℕ) (ρ : Comp → ℕ) (c : Comp) : ℕ :=
  match c.births with
  | e :: rest =>
      if e.scale = m - 1 then
        e.word.length * (succSchedR r₀ J rest.length + 1) + ρ ⟨c.root, rest⟩
      else ρ c
  | [] => ρ c

theorem succRank_succComp_ne (r₀ J m : ℕ) (ρ : Comp → ℕ) (v : Comp) {t : List WordLetter}
    (ht : t ≠ []) :
    succRank r₀ J m ρ (succComp m v t) =
      t.length * (succSchedR r₀ J (compGrade v) + 1) + ρ v := by
  simp [succRank, succComp, ht, compGrade]

theorem succRank_of_scale (r₀ J : ℕ) {m : ℕ} (hm : 1 ≤ m) (ρ : Comp → ℕ) {v : Comp}
    (hv : ∀ e ∈ v.births, m ≤ e.scale) : succRank r₀ J m ρ v = ρ v := by
  unfold succRank
  split
  · next e rest heq =>
    have h1 := hv e (by rw [heq]; exact List.mem_cons_self)
    have hne : ¬ e.scale = m - 1 := by omega
    simp only [hne, ↓reduceIte]
  · rfl

theorem succRank_succComp (r₀ J : ℕ) {m : ℕ} (hm : 1 ≤ m) (ρ : Comp → ℕ) {v : Comp}
    (hv : ∀ e ∈ v.births, m ≤ e.scale) (t : List WordLetter) :
    succRank r₀ J m ρ (succComp m v t) =
      t.length * (succSchedR r₀ J (compGrade v) + 1) + ρ v := by
  by_cases ht : t = []
  · subst ht
    have h1 : succComp m v [] = v := by simp [succComp]
    rw [h1, succRank_of_scale r₀ J hm ρ hv]
    simp
  · exact succRank_succComp_ne r₀ J m ρ v ht

/-! ### Words and components of the extended family -/

theorem length_of_mem_wordsOfLength {A : Finset WordLetter} :
    ∀ {k : ℕ} {t : List WordLetter}, t ∈ wordsOfLength A k → t.length = k
  | 0, t, ht => by
    have h1 : t = [] := by simpa [wordsOfLength] using ht
    rw [h1]
    rfl
  | k + 1, t, ht => by
    simp only [wordsOfLength, Finset.mem_image, Finset.mem_product] at ht
    obtain ⟨x, ⟨-, hx⟩, rfl⟩ := ht
    rw [List.length_append, length_of_mem_wordsOfLength hx]
    rfl

theorem length_of_mem_wordsUpTo {A : Finset WordLetter} {L : ℕ} {t : List WordLetter}
    (ht : t ∈ wordsUpTo A L) : 1 ≤ t.length ∧ t.length ≤ L := by
  simp only [wordsUpTo, Finset.mem_biUnion, Finset.mem_Icc] at ht
  obtain ⟨k, hk, htk⟩ := ht
  rw [length_of_mem_wordsOfLength htk]
  exact hk

/-- A component of the extended family is `(v, 𝔱)` with `v` old and `𝔱` empty or a word of at
most `J + 1` letters. -/
theorem exists_of_mem_succExtComps {m : ℕ} {A : Finset WordLetter} {J : ℕ} {S : Finset Comp}
    {c : Comp} (hc : c ∈ succExtComps m A J S) :
    ∃ v ∈ S, ∃ t : List WordLetter, t.length ≤ J + 1 ∧ c = succComp m v t := by
  simp only [succExtComps, Finset.mem_union, Finset.mem_image, Finset.mem_product] at hc
  rcases hc with hc | ⟨x, ⟨hx1, hx2⟩, rfl⟩
  · exact ⟨c, hc, [], Nat.zero_le _, by simp [succComp]⟩
  · exact ⟨x.1, hx1, x.2, (length_of_mem_wordsUpTo hx2).2, rfl⟩

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-! ### Paths -/

/-- Along a path, a function which does not decrease along the edges does not decrease along the
targets of the steps. -/
theorem stagePath_mono {G : GenStage D hr Dm b j₀} (f : Comp → ℕ)
    (hG : ∀ (v u : CompIn G.comps), Nonempty (G.fam.Γ v u) → f u.1 ≤ f v.1)
    {h : ℕ} (π : StagePath G h) :
    ∀ (i j : ℕ) (hi : i < h) (hj : j < h), i ≤ j →
      f (π.step ⟨i, hi⟩).1.1 ≤ f (π.step ⟨j, hj⟩).1.1 := by
  intro i j hi hj hij
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact le_rfl
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have h1 := ih (by omega) (by omega)
      have h2 := hG (π.step ⟨j + 1, hj⟩).1 (π.step ⟨j + 1, hj⟩).2.1 ⟨(π.step ⟨j + 1, hj⟩).2.2⟩
      rw [π.joined j hj] at h2
      exact h1.trans h2
    · obtain rfl : i = j + 1 := by omega
      exact le_rfl

/-- A strict rank increases from the source to the target of a path. -/
theorem stagePath_rank_src_lt_tgt {G : GenStage D hr Dm b j₀} (ρ : Comp → ℕ)
    (hlt : ∀ (v u : CompIn G.comps), Nonempty (G.fam.Γ v u) → ρ u.1 < ρ v.1)
    {h : ℕ} (π : StagePath G h) (hh : 1 ≤ h) : ρ π.src < ρ π.tgt := by
  have h0 : 0 < h := hh
  have h1 := hlt (π.step ⟨0, h0⟩).1 (π.step ⟨0, h0⟩).2.1 ⟨(π.step ⟨0, h0⟩).2.2⟩
  have h2 := stagePath_mono ρ (fun v u hγ => (hlt v u hγ).le) π 0 (h - 1) h0 (by omega)
    (Nat.zero_le _)
  simp only [StagePath.src, StagePath.tgt, h0, ↓reduceDIte]
  exact lt_of_lt_of_le h1 h2

theorem stagePath_src_mem {G : GenStage D hr Dm b j₀} {h : ℕ} (π : StagePath G h)
    (hh : 1 ≤ h) : π.src ∈ G.comps := by
  have h0 : 0 < h := hh
  simp only [StagePath.src, h0, ↓reduceDIte]
  exact (π.step ⟨0, h0⟩).2.1.2

theorem stagePath_tgt_mem {G : GenStage D hr Dm b j₀} {h : ℕ} (π : StagePath G h)
    (hh : 1 ≤ h) : π.tgt ∈ G.comps := by
  have h0 : 0 < h := hh
  simp only [StagePath.tgt, h0, ↓reduceDIte]
  exact (π.step ⟨h - 1, by omega⟩).1.2

/-- **A path of a stage of depth at most `H` has at most `H` edges.** -/
theorem stagePath_length_le {G : GenStage D hr Dm b j₀} {H : ℕ}
    (hdepth : G.fam.HasDepthAtMost H) {h : ℕ} (π : StagePath G h) : h ≤ H := by
  by_contra hlt
  have hH : H + 1 ≤ h := by omega
  obtain ⟨k, hk⟩ := hdepth fun k : Fin (H + 2) =>
    if hk0 : k.1 = 0 then (π.step ⟨0, by omega⟩).2.1 else (π.step ⟨k.1 - 1, by omega⟩).1
  refine hk.false ?_
  obtain ⟨k, hkH⟩ := k
  have hstep := (π.step ⟨k, by omega⟩).2.2
  have h1 : (if hk0 : (Fin.succ (⟨k, hkH⟩ : Fin (H + 1))).1 = 0 then
      (π.step ⟨0, by omega⟩).2.1 else
      (π.step ⟨(Fin.succ (⟨k, hkH⟩ : Fin (H + 1))).1 - 1, by
        have : (Fin.succ (⟨k, hkH⟩ : Fin (H + 1))).1 = k + 1 := rfl
        omega⟩).1) = (π.step ⟨k, by omega⟩).1 := by
    have h0 : ¬ (Fin.succ (⟨k, hkH⟩ : Fin (H + 1))).1 = 0 := by
      show ¬ k + 1 = 0
      omega
    simp only [h0, ↓reduceDIte]
    rfl
  have h2 : (if hk0 : (Fin.castSucc (⟨k, hkH⟩ : Fin (H + 1))).1 = 0 then
      (π.step ⟨0, by omega⟩).2.1 else
      (π.step ⟨(Fin.castSucc (⟨k, hkH⟩ : Fin (H + 1))).1 - 1, by
        have : (Fin.castSucc (⟨k, hkH⟩ : Fin (H + 1))).1 = k := rfl
        omega⟩).1) = (π.step ⟨k, by omega⟩).2.1 := by
    cases k with
    | zero => rfl
    | succ k =>
      have h0 : ¬ (Fin.castSucc (⟨k + 1, hkH⟩ : Fin (H + 1))).1 = 0 := by
        show ¬ k + 1 = 0
        omega
      simp only [h0, ↓reduceDIte]
      exact (π.joined k (by omega)).symm
  show G.fam.Γ _ _
  rw [h1, h2]
  exact hstep

/-! ### The rank along the sources of the next family -/

/-- **The rank increases along every source** of the next family. -/
theorem succSource_rank_lt {G : GenStage D hr Dm b j₀} (r₀ J : ℕ) {ρ : Comp → ℕ}
    (hm : 1 ≤ G.level) (hscale : ∀ c ∈ G.comps, ∀ e ∈ c.births, G.level ≤ e.scale)
    (hgrade : ∀ (v u : CompIn G.comps), Nonempty (G.fam.Γ v u) → compGrade u.1 ≤ compGrade v.1)
    (hlt : ∀ (v u : CompIn G.comps), Nonempty (G.fam.Γ v u) → ρ u.1 < ρ v.1)
    {A : Finset WordLetter} {J' : ℕ} (s : SuccSource G) (hs : s.Valid A J') :
    succRank r₀ J G.level ρ (s.srcComp G.level) <
      succRank r₀ J G.level ρ (s.tgtComp G.level) := by
  cases s with
  | copyDir t v u γ =>
    show succRank r₀ J G.level ρ (succComp G.level u.1 t) <
      succRank r₀ J G.level ρ (succComp G.level v.1 t)
    rw [succRank_succComp r₀ J hm ρ (hscale u.1 u.2), succRank_succComp r₀ J hm ρ (hscale v.1 v.2)]
    exact succRank_lt (hgrade v u ⟨γ⟩) le_rfl (hlt v u ⟨γ⟩).le (Or.inl (hlt v u ⟨γ⟩))
  | copyQuad t h π =>
    have hh : 1 ≤ h := hs.2.2
    show succRank r₀ J G.level ρ (succComp G.level π.src t) <
      succRank r₀ J G.level ρ (succComp G.level π.tgt t)
    rw [succRank_succComp r₀ J hm ρ (hscale _ (stagePath_src_mem π hh)),
      succRank_succComp r₀ J hm ρ (hscale _ (stagePath_tgt_mem π hh))]
    exact succRank_lt (stagePath_grade_src_le_tgt hgrade π hh) le_rfl
      (stagePath_rank_src_lt_tgt ρ hlt π hh).le (Or.inl (stagePath_rank_src_lt_tgt ρ hlt π hh))
  | letterDiag t u =>
    show succRank r₀ J G.level ρ (succComp G.level u.1 t) <
      succRank r₀ J G.level ρ (succComp G.level u.1 (t ++ [WordLetter.diag]))
    rw [succRank_succComp r₀ J hm ρ (hscale u.1 u.2), succRank_succComp r₀ J hm ρ (hscale u.1 u.2)]
    exact succRank_lt le_rfl (by simp) le_rfl (Or.inr (by simp))
  | letterMean t n h π =>
    have hh : 1 ≤ h := hs.2.2
    show succRank r₀ J G.level ρ (succComp G.level π.src t) <
      succRank r₀ J G.level ρ (succComp G.level π.tgt (t ++ [WordLetter.mean n h]))
    rw [succRank_succComp r₀ J hm ρ (hscale _ (stagePath_src_mem π hh)),
      succRank_succComp r₀ J hm ρ (hscale _ (stagePath_tgt_mem π hh))]
    exact succRank_lt (stagePath_grade_src_le_tgt hgrade π hh) (by simp)
      (stagePath_rank_src_lt_tgt ρ hlt π hh).le (Or.inr (by simp))
  | letterCov t n h a a' π =>
    have hh : 1 ≤ h := hs.2.2
    show succRank r₀ J G.level ρ (succComp G.level π.src t) <
      succRank r₀ J G.level ρ (succComp G.level π.tgt (t ++ [WordLetter.covariance n h a a']))
    rw [succRank_succComp r₀ J hm ρ (hscale _ (stagePath_src_mem π hh)),
      succRank_succComp r₀ J hm ρ (hscale _ (stagePath_tgt_mem π hh))]
    exact succRank_lt (stagePath_grade_src_le_tgt hgrade π hh) (by simp)
      (stagePath_rank_src_lt_tgt ρ hlt π hh).le (Or.inr (by simp))

/-- **One passage keeps the rank invariant**: on the extended next family, the births have scales
at least the new level, `succRank` is at most `r_g` on the components of grade `g`, and it
increases along the edges. -/
theorem depthInv_step {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀} (r₀ : ℕ)
    (hgrade : ∀ (v u : CompIn G.comps), Nonempty (G.fam.Γ v u) → compGrade u.1 ≤ compGrade v.1)
    (hsucc : IsActualSuccessor D P Mn G G')
    (hscale : ∀ c ∈ G.comps, ∀ e ∈ c.births, G.level ≤ e.scale) {ρ : Comp → ℕ}
    (hρ : ∀ c ∈ G.comps, ρ c ≤ succSchedR r₀ Mn.J (compGrade c))
    (hlt : ∀ (v u : CompIn G.comps), Nonempty (G.fam.Γ v u) → ρ u.1 < ρ v.1) :
    (∀ c ∈ G'.comps, ∀ e ∈ c.births, G'.level ≤ e.scale) ∧
      (∀ c ∈ G'.comps, succRank r₀ Mn.J G.level ρ c ≤ succSchedR r₀ Mn.J (compGrade c)) ∧
      ∀ (v u : CompIn G'.comps), Nonempty (G'.fam.Γ v u) →
        succRank r₀ Mn.J G.level ρ u.1 < succRank r₀ Mn.J G.level ρ v.1 := by
  obtain ⟨hm, hlev, hcomps, -, -, -, e, -, -, -, -, -⟩ := hsucc
  refine ⟨fun c hc ev hev => ?_, fun c hc => ?_, fun v u hγ => ?_⟩
  · rw [hcomps] at hc
    obtain ⟨v, hv, t, -, rfl⟩ := exists_of_mem_succExtComps hc
    rw [hlev]
    by_cases ht : t = []
    · subst ht
      have h1 : succComp G.level v [] = v := by simp [succComp]
      rw [h1] at hev
      have := hscale v hv ev hev
      omega
    · have h1 : (succComp G.level v t).births = ⟨G.level - 1, t, ht⟩ :: v.births := by
        simp [succComp, ht]
      rw [h1, List.mem_cons] at hev
      rcases hev with rfl | hev
      · exact le_rfl
      · have := hscale v hv ev hev
        omega
  · rw [hcomps] at hc
    obtain ⟨v, hv, t, htl, rfl⟩ := exists_of_mem_succExtComps hc
    rw [succRank_succComp r₀ Mn.J hm ρ (hscale v hv)]
    by_cases ht : t = []
    · subst ht
      rw [compGrade_succComp_nil]
      simpa using hρ v hv
    · rw [compGrade_succComp_ne G.level v ht]
      exact succRank_bound htl (hρ v hv)
  · obtain ⟨γ'⟩ := hγ
    have hs := (e v u γ').2
    have h1 := succSource_rank_lt r₀ Mn.J hm hscale hgrade hlt (e v u γ').1 hs.1
    rwa [hs.2.1, hs.2.2] at h1

/-- **The rank invariant of the cascade.** On every stage: the grades are at most `H`, the births
have scales at least the level, and there is a rank at most `r_g` on the components of grade `g`
which increases along the edges. -/
theorem depthInv_of_cascade {P : ProvParams} {Mn : SuccMenu} {seed : GenStage D hr Dm b j₀}
    {r₀ : ℕ} (hseedB : ∀ v : CompIn seed.comps, v.1.births = [])
    (hseedD : seed.fam.HasDepthAtMost r₀) {G : GenStage D hr Dm b j₀}
    (hG : IsCascadeStage D P Mn seed G) :
    (∀ c ∈ G.comps, compGrade c ≤ Mn.H) ∧
      (∀ c ∈ G.comps, ∀ e ∈ c.births, G.level ≤ e.scale) ∧
      ∃ ρ : Comp → ℕ, (∀ c ∈ G.comps, ρ c ≤ succSchedR r₀ Mn.J (compGrade c)) ∧
        ∀ (v u : CompIn G.comps), Nonempty (G.fam.Γ v u) → ρ u.1 < ρ v.1 := by
  classical
  induction hG with
  | seed =>
    refine ⟨fun c hc => ?_, fun c hc ev hev => ?_,
      fun c => if hc : c ∈ seed.comps then CycleWords.familyDepthRank seed.fam r₀ ⟨c, hc⟩ else 0,
      fun c hc => ?_, fun v u hγ => ?_⟩
    · have h1 : compGrade c = 0 := by
        have h0 : c.births = [] := hseedB ⟨c, hc⟩
        simp [compGrade, h0]
      omega
    · rw [hseedB ⟨c, hc⟩] at hev
      simp at hev
    · have h1 : compGrade c = 0 := by
        have h0 : c.births = [] := hseedB ⟨c, hc⟩
        simp [compGrade, h0]
      simp only [h1, hc, ↓reduceDIte]
      exact CycleWords.familyDepthRank_le seed.fam r₀ ⟨c, hc⟩
    · simp only [u.2, v.2, ↓reduceDIte]
      exact CycleWords.familyDepthRank_strict seed.fam r₀ hseedD hγ
  | @step G G' hc hsucc ih =>
    obtain ⟨-, hscale, ρ, hρ, hlt⟩ := ih
    obtain ⟨hs', hρ', hlt'⟩ :=
      depthInv_step r₀ (grade_mono_of_cascade hseedB hc) hsucc hscale hρ hlt
    refine ⟨fun c hc' => (Finset.mem_filter.mp hc').2.1,
      fun c hc' => hs' c (Finset.mem_filter.mp hc').1, succRank r₀ Mn.J G.level ρ,
      fun c hc' => hρ' c (Finset.mem_filter.mp hc').1, fun v u hγ =>
        hlt' ⟨v.1, (Finset.mem_filter.mp v.2).1⟩ ⟨u.1, (Finset.mem_filter.mp u.2).1⟩ hγ⟩

/-- **The depth of the stages of the cascade** (the depth schedule): every
stage of the cascade from a seed of depth `r₀` whose components have no births has depth at most
`r_H = succSchedR r₀ J H`. -/
theorem cascade_depth {P : ProvParams} {Mn : SuccMenu} {seed : GenStage D hr Dm b j₀} {r₀ : ℕ}
    (hseedB : ∀ v : CompIn seed.comps, v.1.births = []) (hseedD : seed.fam.HasDepthAtMost r₀)
    {G : GenStage D hr Dm b j₀} (hG : IsCascadeStage D P Mn seed G) :
    G.fam.HasDepthAtMost (succSchedR r₀ Mn.J Mn.H) := by
  obtain ⟨hgr, -, ρ, hρ, hlt⟩ := depthInv_of_cascade hseedB hseedD hG
  exact hasDepthAtMost_of_rank G.fam (fun v => ρ v.1)
    (fun v => (hρ v.1 v.2).trans (AVRegularity.Providers.CascadeInvariants.succSchedR_mono r₀ Mn.J (hgr v.1 v.2))) hlt

section GeneratedSeed

variable [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

/-- **The depth of the stages of the cascade from a generated seed**: `IsGeneratedSeed` (depth
`r₀`, no births) and `IsCascadeStage` give the depth `r_H = succSchedR r₀ J H`. -/
theorem cascade_depth_of_generatedSeed {law : BirthLaw} {P P' : ProvParams}
    {seedK freshK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {M : ℕ}
    {kS : InvConsts} {seed : GenStage D hr Dm b j₀} {n : ℕ} {tS tf Ce τe : ℝ} {r₀ D₀ : ℕ}
    (h : IsGeneratedSeed law P seedK freshK φ₀ hφ₀ M kS seed n tS tf Ce τe r₀ D₀)
    {Mn : SuccMenu} {G : GenStage D hr Dm b j₀} (hG : IsCascadeStage D P' Mn seed G) :
    G.fam.HasDepthAtMost (succSchedR r₀ Mn.J Mn.H) :=
  cascade_depth h.2.1 h.2.2.2.2.1 hG

/-- The paths of a stage of the cascade from a generated seed have at most `r_H` edges. -/
theorem cascade_path_length_le_of_generatedSeed {law : BirthLaw} {P P' : ProvParams}
    {seedK freshK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {M : ℕ}
    {kS : InvConsts} {seed : GenStage D hr Dm b j₀} {n : ℕ} {tS tf Ce τe : ℝ} {r₀ D₀ : ℕ}
    (h : IsGeneratedSeed law P seedK freshK φ₀ hφ₀ M kS seed n tS tf Ce τe r₀ D₀)
    {Mn : SuccMenu} {G : GenStage D hr Dm b j₀} (hG : IsCascadeStage D P' Mn seed G) {k : ℕ}
    (π : StagePath G k) : k ≤ succSchedR r₀ Mn.J Mn.H :=
  stagePath_length_le (cascade_depth_of_generatedSeed h hG) π

end GeneratedSeed

end AVRegularity.Providers.CascadeInvariants
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the scale facts of a passage.** `PassScales D m C` collects what the ledger of the
passage `m → m-1` uses from the diffusivity and covariance ledger of the band chain
(`CycleReference.bandChain_uniform_ledger`), for `2 ≤ m ≤ M`:
* `κ_m ≤ κ_{m-1}`, both positive (and equal to the clamped diffusivities `D.kap`);
* the lift length `ρ_m = √(κ_{m-1}τ_m'')` is positive and at most the wavelength `ε_{m-1}`;
* the displacement `d_* = ε_m√(κ_{m-1}/κ_m)` satisfies `d_*² = κ_{m-1}ℓ_m²`, `ε_m ≤ d_*` and
  `d_*/ρ_m ≤ C ε_{m-1}^{3δ}`;
* the covariance satisfies `|𝖧_m| ≤ C ε_{m-1}^δ ρ_m²`.
`exists_passScales` provides them with one constant, for `Λ` beyond a threshold that also makes
`C ε_{m-1}^c ≤ 1` (so that `ρ_m ≤ C ε_{m-1}^{1+c} ≤ ε_{m-1}` at every level `m ≥ 2`). The
wavelengths decrease (`eps_succ_le`) and `ε_k ≤ Λ⁻¹` for `k ≥ 1` (`eps_le_inv`). -/

/-- The wavelengths decrease towards the fine levels. -/
theorem eps_succ_le {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (k : ℕ) :
    ocEpsilon q Λ (k + 1) ≤ ocEpsilon q Λ k := by
  have h := Scales.epsilon_ratio_lower (q := q) (Λ := Λ) (m := k + 1) hq hΛ (by omega)
  have hpos : 0 < ocEpsilon q Λ (k + 1) := Construction.Stream.ocEpsilon_pos (by omega)
  rw [Nat.add_sub_cancel, ge_iff_le, le_div_iff₀ hpos] at h
  have hΛr : (1 : ℝ) ≤ Λ := by exact_mod_cast (by omega : 1 ≤ Λ)
  calc ocEpsilon q Λ (k + 1) = 1 * ocEpsilon q Λ (k + 1) := (one_mul _).symm
    _ ≤ Λ * ocEpsilon q Λ (k + 1) := mul_le_mul_of_nonneg_right hΛr hpos.le
    _ ≤ ocEpsilon q Λ k := h

/-- The wavelengths are antitone in the level. -/
theorem eps_le_of_le {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) {k l : ℕ} (hkl : k ≤ l) :
    ocEpsilon q Λ l ≤ ocEpsilon q Λ k := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact (eps_succ_le hq hΛ l).trans ih

/-- `ε_k ≤ Λ⁻¹` for `k ≥ 1`. -/
theorem eps_le_inv {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) {k : ℕ} (hk : 1 ≤ k) :
    ocEpsilon q Λ k ≤ (Λ : ℝ)⁻¹ := by
  have h := Scales.epsilon_ratio_lower (q := q) (Λ := Λ) (m := 1) hq hΛ le_rfl
  have hpos : 0 < ocEpsilon q Λ 1 := Construction.Stream.ocEpsilon_pos (by omega)
  have h0 : ocEpsilon q Λ (1 - 1) = 1 := by simp [ocEpsilon]
  rw [h0, ge_iff_le, le_div_iff₀ hpos] at h
  have hΛpos : (0 : ℝ) < Λ := by exact_mod_cast (by omega : 0 < Λ)
  refine (eps_le_of_le hq hΛ hk).trans ?_
  rw [← one_div, le_div_iff₀ hΛpos, mul_comm]
  exact h

/-- **The scale facts of the passage `m → m-1`** used by the ledger. -/
structure PassScales (D : OCData) (m : ℕ) (Cu : ℝ) : Prop where
  /-- The clamped diffusivity of the level. -/
  hκm : D.kap m = D.κ m
  /-- The clamped diffusivity of the coarser level. -/
  hκm' : D.kap (m - 1) = D.κ (m - 1)
  /-- The diffusivity of the level is positive. -/
  hκ0 : 0 < D.kap m
  /-- The diffusivity of the coarser level is positive. -/
  hκ1 : 0 < D.kap (m - 1)
  /-- The diffusivities grow towards the coarse levels. -/
  hκle : D.kap m ≤ D.kap (m - 1)
  /-- The lift length is positive. -/
  hρ0 : 0 < liftLength D m
  /-- The lift length is at most the coarser wavelength. -/
  hρE : liftLength D m ≤ D.eps (m - 1)
  /-- `d_*² = κ_{m-1} ℓ_m²`. -/
  hDst : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ 2 = D.kap (m - 1) * D.cellScaleSq m
  /-- `ε_m ≤ d_*`. -/
  hεd : D.eps m ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))
  /-- `d_*/ρ_m ≤ C ε_{m-1}^{3δ}`. -/
  hDρ : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / liftLength D m ≤
    Cu * D.eps (m - 1) ^ (3 * ocDelta D.α D.q)
  /-- `|𝖧_m| ≤ C ε_{m-1}^δ ρ_m²`. -/
  hH : ∀ (t : ℝ) (i j : Fin 2),
    |ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) 0 t i j| ≤
      Cu * D.eps (m - 1) ^ ocDelta D.α D.q * liftLength D m ^ 2

/-- **The scale facts of every passage of the band chain**, with one constant, for `Λ` beyond a
threshold. -/
theorem exists_passScales {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Cu : ℝ, 1 ≤ Cu ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ D : OCData, D.α = α → D.q = q → D.ζ = ζ →
      Λ₀ ≤ D.Λ → IsOCBandChain α q D.Λ ζ D.term D.κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ D.term → PassScales D m Cu := by
  obtain ⟨C, hC, Λ₁, hΛ₁, hled⟩ := CycleReference.bandChain_uniform_ledger hα0 hα1 hs0 hs1 hq hζ
  have hc := ocC_pos_of_admissible hα0 hq
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC, max Λ₁ ⌈C ^ (1 / ocC α q)⌉₊, le_max_of_le_left hΛ₁, ?_⟩
  intro D hDα hDq hDζ hΛ hκ m hm hmM
  subst hDα hDq hDζ
  have hΛ1 : Λ₁ ≤ D.Λ := (le_max_left _ _).trans hΛ
  have hΛ128 : 128 ≤ D.Λ := hΛ₁.trans hΛ1
  have hΛone : 1 ≤ D.Λ := by omega
  have hq1 : 1 < D.q := hq.1
  have hΛC : C ^ (1 / ocC D.α D.q) ≤ (D.Λ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hΛ)
  obtain ⟨-, h2⟩ := hled D.Λ hΛ1 D.term (by omega) D.κ hκ
  obtain ⟨hνB, -, -, -, hρas, -, -, hDρ, -, -, -, -, -, -, -, hcov⟩ :=
    h2 m hm hmM (D.κ m) (D.κ (m - 1)) rfl rfl
  have hκm : D.kap m = D.κ m := by
    unfold OCData.kap
    rw [min_eq_left hmM]
  have hκm' : D.kap (m - 1) = D.κ (m - 1) := by
    unfold OCData.kap
    rw [min_eq_left (by omega)]
  have hν : 0 < D.κ m := CycleReference.bandChain_pos hΛone hζ hκ hmM
  have hB : 0 < D.κ (m - 1) := CycleReference.bandChain_pos hΛone hζ hκ (by omega)
  have hε : 0 < ocEpsilon D.q D.Λ (m - 1) := Construction.Stream.ocEpsilon_pos hΛone
  have hεm : 0 < ocEpsilon D.q D.Λ m := Construction.Stream.ocEpsilon_pos hΛone
  have hρ0 : 0 < liftLength D m := by
    unfold liftLength
    exact Real.sqrt_pos.mpr (mul_pos hB (Construction.Stream.ocTauPP_pos hΛone))
  have hρeq : liftLength D m = ocRh D.α D.q D.Λ m (D.κ (m - 1)) := rfl
  -- `C ε_{m-1}^c ≤ 1`
  have hΛpos : (0 : ℝ) < D.Λ := by exact_mod_cast (by omega : 0 < D.Λ)
  have hCΛ : C ≤ (D.Λ : ℝ) ^ ocC D.α D.q := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hC0.le _) hΛC hc.le
    rwa [← Real.rpow_mul hC0.le, one_div_mul_cancel hc.ne', Real.rpow_one] at h1
  have hsmall : C * ocEpsilon D.q D.Λ (m - 1) ^ ocC D.α D.q ≤ 1 := by
    have h1 : ocEpsilon D.q D.Λ (m - 1) ^ ocC D.α D.q ≤ ((D.Λ : ℝ) ^ ocC D.α D.q)⁻¹ := by
      rw [← Real.inv_rpow hΛpos.le]
      exact Real.rpow_le_rpow hε.le (eps_le_inv hq1 hΛ128 (by omega)) hc.le
    have hΛc : 0 < (D.Λ : ℝ) ^ ocC D.α D.q := Real.rpow_pos_of_pos hΛpos _
    calc C * ocEpsilon D.q D.Λ (m - 1) ^ ocC D.α D.q
        ≤ (D.Λ : ℝ) ^ ocC D.α D.q * ((D.Λ : ℝ) ^ ocC D.α D.q)⁻¹ :=
          mul_le_mul hCΛ h1 (Real.rpow_nonneg hε.le _) hΛc.le
      _ = 1 := mul_inv_cancel₀ hΛc.ne'
  refine ⟨hκm, hκm', hκm ▸ hν, hκm' ▸ hB, by rw [hκm, hκm']; exact hνB, hρ0, ?_, ?_, ?_, ?_, ?_⟩
  · -- `ρ_m ≤ ε_{m-1}`
    have h1 : ocEpsilon D.q D.Λ (m - 1) ^ (1 + ocC D.α D.q) =
        ocEpsilon D.q D.Λ (m - 1) * ocEpsilon D.q D.Λ (m - 1) ^ ocC D.α D.q := by
      rw [Real.rpow_add hε, Real.rpow_one]
    rw [hρeq]
    calc ocRh D.α D.q D.Λ m (D.κ (m - 1))
        ≤ C * ocEpsilon D.q D.Λ (m - 1) ^ (1 + ocC D.α D.q) := hρas.2
      _ = (C * ocEpsilon D.q D.Λ (m - 1) ^ ocC D.α D.q) * ocEpsilon D.q D.Λ (m - 1) := by
          rw [h1]; ring
      _ ≤ 1 * ocEpsilon D.q D.Λ (m - 1) := mul_le_mul_of_nonneg_right hsmall hε.le
      _ = D.eps (m - 1) := one_mul _
  · -- `d_*² = κ_{m-1} ℓ_m²`
    rw [hκm, hκm']
    unfold ocDStar OCData.cellScaleSq OCData.eps
    rw [hκm, mul_pow, Real.sq_sqrt (div_nonneg hB.le hν.le)]
    ring
  · -- `ε_m ≤ d_*`
    rw [hκm, hκm']
    unfold ocDStar
    exact le_mul_of_one_le_right hεm.le (Real.one_le_sqrt.mpr ((one_le_div hν).mpr hνB))
  · rw [hκm, hκm', hρeq]
    exact hDρ
  · intro t i j
    have h1 := (hcov 0 t i j).2.2.2
    rwa [div_le_iff₀ (pow_pos (hρeq ▸ hρ0) 2), ← hρeq] at h1

/-- The fresh length of a birth level is at most its wavelength. -/
theorem freshLength_le_eps_of_passScales {D : OCData} {Cu cr : ℝ} (hcr1 : cr ≤ 1) {b' : ℕ} (h : PassScales D (b' + 1) Cu) : freshLength D cr b' ≤ D.eps b' := by
  have hρ := h.hρ0
  have hE := h.hρE
  rw [Nat.add_sub_cancel] at hE
  have e : freshLength D cr b' = cr * liftLength D (b' + 1) := by
    unfold freshLength liftLength
    rw [Nat.add_sub_cancel]
  rw [e]
  calc cr * liftLength D (b' + 1) ≤ 1 * liftLength D (b' + 1) :=
        mul_le_mul_of_nonneg_right hcr1 hρ.le
    _ = liftLength D (b' + 1) := one_mul _
    _ ≤ D.eps b' := hE

end AVRegularity.Providers.CascadeInvariants
end
end
