-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq

public section

section
namespace AVRegularity.IterationPassage.Cascade

/-! **Downward recursion of a family over the levels of the cascade**.

For a fixed run of the cascade the families `U_j` of a datum are chosen level by level from `n`
down to `m₀`: `U_{j-1}` is a retained solution of the passage `j`, which exists by the output of
that passage. The type of `U_j` depends on `j` (through the stage of level `j`).
`exists_downward_family` does this recursion once, for a type family `T j`, an invariant `P j` and
a step relation `R j : T j → T (j - 1) → Prop`: no cast appears in its statement.

`exists_upward_family` is the upward recursion from `m₀` (for the representation `rep`).

Special cases. `m₀ = n`: the given start. `n = m₀ + 1`: one step. The family outside `[m₀, n]` is
the given default family. -/

section
universe u

/-- Downward dependent recursion over the levels `m₀ ≤ j ≤ n`, from the start `X₀ n`. -/
theorem exists_downward_family {T : ℕ → Type u} (n : ℕ) (P : (j : ℕ) → T j → Prop)
    (R : (j : ℕ) → T j → T (j - 1) → Prop) (X₀ : (j : ℕ) → T j) (hstart : P n (X₀ n))
    (m₀ : ℕ) (hm : m₀ ≤ n)
    (hstep : ∀ j, m₀ < j → j ≤ n → ∀ x : T j, P j x → ∃ y : T (j - 1), R j x y ∧ P (j - 1) y) :
    ∃ X : (j : ℕ) → T j, X n = X₀ n ∧ (∀ j, m₀ ≤ j → j ≤ n → P j (X j)) ∧
      ∀ j, m₀ < j → j ≤ n → R j (X j) (X (j - 1)) := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d, n = m₀ + d := ⟨n - m₀, by omega⟩
  clear hm
  induction d generalizing m₀ with
  | zero =>
    refine ⟨X₀, rfl, fun j hj hjn => ?_, fun j hj hjn => absurd hjn (by omega)⟩
    obtain rfl : j = m₀ + 0 := by omega
    exact hstart
  | succ d ih =>
    have hn : m₀ + (d + 1) = m₀ + 1 + d := by omega
    rw [hn] at hstart hstep ⊢
    obtain ⟨X, hXn, hP, hR⟩ := ih (m₀ + 1) hstart
      (fun j hj hjn x hx => hstep j (by omega) hjn x hx)
    obtain ⟨y, hRy, hPy⟩ := hstep (m₀ + 1) (by omega) (by omega) (X (m₀ + 1))
      (hP (m₀ + 1) le_rfl (by omega))
    have hy : ∀ j, j ≠ m₀ → Function.update X m₀ y j = X j := fun j hj =>
      Function.update_of_ne hj y X
    refine ⟨Function.update X m₀ y, ?_, fun j hj hjn => ?_, fun j hj hjn => ?_⟩
    · rw [hy _ (by omega)]
      exact hXn
    · by_cases hjm : j = m₀
      · subst hjm
        rw [Function.update_self]
        exact hPy
      · rw [hy j hjm]
        exact hP j (by omega) hjn
    · by_cases hjm : j = m₀ + 1
      · subst hjm
        rw [hy _ (by omega)]
        have he : Function.update X m₀ y (m₀ + 1 - 1) = y := Function.update_self m₀ y X
        rw [he]
        exact hRy
      · rw [hy j (by omega), hy (j - 1) (by omega)]
        exact hR j (by omega) hjn

/-- Upward dependent recursion from the level `m₀`: `X m₀ = base m₀` and
`X (k + 1) = step k (X k)` for `k ≥ m₀` (the representation `rep` of the cascade). -/
theorem exists_upward_family {T : ℕ → Type u} (m₀ : ℕ) (base : (j : ℕ) → T j)
    (step : (k : ℕ) → T k → T (k + 1)) :
    ∃ X : (j : ℕ) → T j, X m₀ = base m₀ ∧ ∀ k, m₀ ≤ k → X (k + 1) = step k (X k) := by
  refine ⟨fun j => Nat.rec (base 0) (fun k r => if k < m₀ then base (k + 1) else step k r) j,
    ?_, fun k hk => ?_⟩
  · cases m₀ with
    | zero => rfl
    | succ k =>
      show (if k < k + 1 then base (k + 1) else step k _) = base (k + 1)
      simp only [Nat.lt_add_one, ↓reduceIte]
  · show (if k < m₀ then base (k + 1) else step k _) = step k _
    simp only [not_lt.mpr hk, ↓reduceIte]
end

/-! **The downward recursion of the cascade, abstractly**.

The run of the cascade from the seed at level `n` down to `m₀` is a recursion in `i = n - j`
whose step chooses an actual successor, a preparation time and a preparation of the current stage.
The type of the preparation depends on the stage, so the recursion is dependent. This module does
it once for abstract predicates; `Cascade/Run.lean` instantiates it.

* `exists_dependent_run`: dependent recursion with an invariant and total choice.
* `exists_cascade_run`: the frame of the cascade for abstract predicates: `Cas` (cascade stage),
  `InvP j t_A` (invariant of level `j` from `t_A`), `Succ` (actual successor), `ret j` (retained
  part), `Frame`, `Outp` (frame and output of one passage), waits `τ, τ'`. The times are
  `a_n = s_n = t_S`, `a_{j-1} = a_j + 3τ_j`, `s_{j-1} = t_p^{(j)}`, and the preparation of passage
  `j` starts at `r_j = max{s_j, a_j + 3τ_j}`. The invariant of the recursion at level `j` is
  `t_S ≤ a_j ≤ s_j` and `s_j - t_S ≤ ∑_{j<k≤n}(3τ_k + 4τ'_k)`.

Special cases. `n = m₀ + 1`: one step. `τ = τ' = 0`: all times equal `t_S` and the hypotheses on the
wait reduce to `0 < t₀`. The seed alone (`m₀ = n`) is excluded by `m₀ < n`, as in the statement. -/

section
universe u v

/-- Dependent recursion with an invariant: the output type of a step depends on the state. -/
theorem exists_dependent_run {St : Type u} {Out : St → Type v} [∀ σ, Nonempty (Out σ)]
    (Inv : ℕ → St → Prop) (Good : ℕ → (σ : St) → Out σ → Prop)
    (next : ℕ → (σ : St) → Out σ → St) (L : ℕ) (σ₀ : St) (h0 : Inv 0 σ₀)
    (hex : ∀ i σ, i < L → Inv i σ → ∃ o, Good i σ o)
    (hstep : ∀ i σ o, i < L → Inv i σ → Good i σ o → Inv (i + 1) (next i σ o)) :
    ∃ (σs : ℕ → St) (os : (i : ℕ) → Out (σs i)), σs 0 = σ₀ ∧
      (∀ i, σs (i + 1) = next i (σs i) (os i)) ∧ (∀ i, i ≤ L → Inv i (σs i)) ∧
      ∀ i, i < L → Good i (σs i) (os i) := by
  classical
  let pick : ℕ → (σ : St) → Out σ := fun i σ => Classical.epsilon (Good i σ)
  let σs : ℕ → St := fun i => Nat.rec σ₀ (fun i σ => next i σ (pick i σ)) i
  have hInv : ∀ i, i ≤ L → Inv i (σs i) := by
    intro i
    induction i with
    | zero => exact fun _ => h0
    | succ i ih =>
      intro hi
      have hi' : i < L := hi
      have hI := ih hi'.le
      exact hstep i (σs i) (pick i (σs i)) hi' hI (Classical.epsilon_spec (hex i (σs i) hi' hI))
  exact ⟨σs, fun i => pick i (σs i), rfl, fun _ => rfl, hInv,
    fun i hi => Classical.epsilon_spec (hex i (σs i) hi (hInv i hi.le))⟩

/-- The state of the run at one level: the stage, the history start and the birth time. -/
structure RunState (Stg : Type u) where
  /-- The stage. -/
  G : Stg
  /-- The history-window start `a_j`. -/
  a : ℝ
  /-- The birth time `s_j`. -/
  s : ℝ

/-- The choice of one step: the successor, the preparation time and the preparation. -/
structure StepOut {Stg : Type u} (PrepT : Stg → Type v) (G : Stg) where
  /-- The actual successor. -/
  ext : Stg
  /-- The preparation time. -/
  tp : ℝ
  /-- The preparation. -/
  Preg : PrepT G

instance {Stg : Type u} (PrepT : Stg → Type v) [∀ G, Nonempty (PrepT G)] (G : Stg) :
    Nonempty (StepOut PrepT G) :=
  ⟨⟨G, 0, Classical.choice inferInstance⟩⟩

/-- The wait bound of one step: `max{s, a + 3τ_j} + 4τ'_j - t_S ≤ ∑_{j-1<k≤n}(3τ_k + 4τ'_k)`. -/
theorem restart_wait_le (τ τ' : ℕ → ℝ) (hτ : ∀ k, 0 ≤ τ k) (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n)
    (tS a s : ℝ) (has : a ≤ s) (hs : s - tS ≤ ∑ k ∈ Finset.Ioc j n, (3 * τ k + 4 * τ' k)) :
    max s (a + 3 * τ j) + 4 * τ' j - tS ≤ ∑ k ∈ Finset.Ioc (j - 1) n, (3 * τ k + 4 * τ' k) := by
  have hsplit : ∑ k ∈ Finset.Ioc (j - 1) n, (3 * τ k + 4 * τ' k) =
      (3 * τ j + 4 * τ' j) + ∑ k ∈ Finset.Ioc j n, (3 * τ k + 4 * τ' k) := by
    have hone : Finset.Ioc (j - 1) j = {j} := by
      have h := Nat.Ioc_succ_singleton (b := j - 1)
      rwa [Nat.sub_add_cancel hj] at h
    rw [← Finset.sum_Ioc_consecutive (fun k => 3 * τ k + 4 * τ' k) (Nat.sub_le j 1) hjn,
      hone, Finset.sum_singleton]
  have hmax : max s (a + 3 * τ j) ≤ s + 3 * τ j :=
    max_le (by linarith [hτ j]) (by linarith)
  rw [hsplit]
  linarith

/-- The tail of the wait from a level `j ≥ m₀` is at most the wait from `m₀`. -/
theorem wait_tail_le (τ τ' : ℕ → ℝ) (hτ : ∀ k, 0 ≤ τ k) (hτ' : ∀ k, 0 ≤ τ' k) (n m₀ j : ℕ)
    (hj : m₀ ≤ j) :
    ∑ k ∈ Finset.Ioc j n, (3 * τ k + 4 * τ' k) ≤ ∑ k ∈ Finset.Ioc m₀ n, (3 * τ k + 4 * τ' k) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_left hj)
    (fun k _ _ => by linarith [hτ k, hτ' k])

section Run

variable {Stg : Type u} {PrepT : Stg → Type v}

/-- The invariant of the run at level `j`. -/
def RunInv (level : Stg → ℕ) (Cas : Stg → Prop) (InvP : ℕ → ℝ → Stg → Prop) (τ τ' : ℕ → ℝ)
    (n : ℕ) (tS : ℝ) (j : ℕ) (σ : RunState Stg) : Prop :=
  level σ.G = j ∧ Cas σ.G ∧ InvP j σ.a σ.G ∧ tS ≤ σ.a ∧ σ.a ≤ σ.s ∧
    σ.s - tS ≤ ∑ k ∈ Finset.Ioc j n, (3 * τ k + 4 * τ' k)

/-- The step of the run at level `j`: successor, remaining window, frame and output. -/
def RunGood (Succ : Stg → Stg → Prop) (ret : ℕ → Stg → Stg)
    (Frame : (G : Stg) → Stg → ℕ → ℝ → ℝ → ℝ → PrepT G → Prop)
    (Outp : (G : Stg) → Stg → ℕ → ℝ → ℝ → PrepT G → Prop) (τ τ' : ℕ → ℝ) (tf : ℝ)
    (j : ℕ) (σ : RunState Stg) (o : StepOut PrepT σ.G) : Prop :=
  Succ σ.G o.ext ∧ max σ.s (σ.a + 3 * τ j) + 4 * τ' j ≤ tf ∧
    Frame σ.G (ret j o.ext) j σ.a (max σ.s (σ.a + 3 * τ j)) o.tp o.Preg ∧
    Outp σ.G (ret j o.ext) j (max σ.s (σ.a + 3 * τ j)) o.tp o.Preg

/-- The next state of the run. -/
def runNext (ret : ℕ → Stg → Stg) (τ : ℕ → ℝ) (j : ℕ) (σ : RunState Stg)
    (o : StepOut PrepT σ.G) : RunState Stg :=
  ⟨ret j o.ext, σ.a + 3 * τ j, o.tp⟩

/-- **The frame of the cascade for abstract predicates.** -/
theorem exists_cascade_run [∀ G, Nonempty (PrepT G)]
    (level : Stg → ℕ) (Cas : Stg → Prop) (InvP : ℕ → ℝ → Stg → Prop) (Succ : Stg → Stg → Prop)
    (ret : ℕ → Stg → Stg)
    (Frame : (G : Stg) → Stg → ℕ → ℝ → ℝ → ℝ → PrepT G → Prop)
    (Outp : (G : Stg) → Stg → ℕ → ℝ → ℝ → PrepT G → Prop)
    (τ τ' : ℕ → ℝ) (hτ : ∀ k, 0 ≤ τ k) (hτ' : ∀ k, 0 ≤ τ' k)
    (seed : Stg) (n m₀ : ℕ) (tS t₀ tf T₀ : ℝ) (hm₀ : m₀ < n)
    (hwait : ∑ k ∈ Finset.Ioc m₀ n, (3 * τ k + 4 * τ' k) < t₀) (ht₀ : tS + t₀ < tf)
    (hT₀ : tf - tS ≤ T₀)
    (hlevel : level seed = n) (hcas : Cas seed) (hinv : InvP n tS seed)
    (hsucc : ∀ j G tA, m₀ < j → j ≤ n → Cas G → level G = j → tS ≤ tA → InvP j tA G →
      ∃ G', Succ G G')
    (hpass : ∀ j G G' tA s₀, m₀ < j → j ≤ n → tS ≤ tA → tA + 3 * τ j ≤ s₀ →
      s₀ + 4 * τ' j ≤ tf → tf - s₀ ≤ T₀ → Cas G → level G = j → InvP j tA G → Succ G G' →
      ∃ (tp : ℝ) (Preg : PrepT G),
        Frame G (ret j G') j tA s₀ tp Preg ∧ Outp G (ret j G') j s₀ tp Preg)
    (hframe : ∀ j G Gr tA s₀ tp (Preg : PrepT G), level G = j → Frame G Gr j tA s₀ tp Preg →
      s₀ ≤ tp ∧ tp ≤ s₀ + 4 * τ' j ∧ Cas Gr ∧ InvP (j - 1) (tA + 3 * τ j) Gr)
    (hretlevel : ∀ j G G', level G = j → Succ G G' → level (ret j G') = j - 1) :
    ∃ (stage ext : ℕ → Stg) (hist st tp : ℕ → ℝ) (Preg : (j : ℕ) → PrepT (stage j)),
      stage n = seed ∧ hist n = tS ∧ st n = tS ∧ st m₀ ≤ tS + t₀ ∧
      (∀ j, m₀ ≤ j → j ≤ n → level (stage j) = j ∧ Cas (stage j) ∧ InvP j (hist j) (stage j) ∧
        hist j ≤ st j ∧ st j - tS ≤ ∑ k ∈ Finset.Ioc j n, (3 * τ k + 4 * τ' k)) ∧
      ∀ j, m₀ < j → j ≤ n → Succ (stage j) (ext j) ∧ stage (j - 1) = ret j (ext j) ∧
        hist (j - 1) = hist j + 3 * τ j ∧ st (j - 1) = tp j ∧
        max (st j) (hist j + 3 * τ j) + 4 * τ' j ≤ tf ∧
        Frame (stage j) (stage (j - 1)) j (hist j) (max (st j) (hist j + 3 * τ j)) (tp j)
          (Preg j) ∧
        Outp (stage j) (stage (j - 1)) j (max (st j) (hist j + 3 * τ j)) (tp j) (Preg j) := by
  -- the wait of a step at a level `j > m₀`
  have hwin : ∀ j (σ : RunState Stg), m₀ < j → j ≤ n → σ.a ≤ σ.s →
      σ.s - tS ≤ ∑ k ∈ Finset.Ioc j n, (3 * τ k + 4 * τ' k) →
      max σ.s (σ.a + 3 * τ j) + 4 * τ' j - tS < t₀ := by
    intro j σ hj hjn has hs
    exact (restart_wait_le τ τ' hτ n j (by omega) hjn tS σ.a σ.s has hs).trans_lt
      ((wait_tail_le τ τ' hτ hτ' n m₀ (j - 1) (by omega)).trans_lt hwait)
  obtain ⟨σs, os, hσ0, hσs, hI, hG⟩ := exists_dependent_run
    (Out := fun σ : RunState Stg => StepOut PrepT σ.G)
    (fun i σ => RunInv level Cas InvP τ τ' n tS (n - i) σ)
    (fun i σ o => RunGood Succ ret Frame Outp τ τ' tf (n - i) σ o)
    (fun i σ o => runNext ret τ (n - i) σ o) (n - m₀) ⟨seed, tS, tS⟩
    ⟨hlevel, hcas, hinv, le_rfl, le_rfl, by simp⟩
    (by
      intro i σ hi hσ
      obtain ⟨hlev, hc, hiv, htA, has, hs⟩ := hσ
      have hj : m₀ < n - i := by omega
      have hjn : n - i ≤ n := Nat.sub_le n i
      obtain ⟨G', hG'⟩ := hsucc (n - i) σ.G σ.a hj hjn hc hlev htA hiv
      have hw := hwin (n - i) σ hj hjn has hs
      have hr : σ.s ≤ max σ.s (σ.a + 3 * τ (n - i)) := le_max_left _ _
      obtain ⟨tp, Preg, hF, hO⟩ := hpass (n - i) σ.G G' σ.a (max σ.s (σ.a + 3 * τ (n - i))) hj
        hjn htA (le_max_right _ _) (by linarith) (by linarith) hc hlev hiv hG'
      exact ⟨⟨G', tp, Preg⟩, hG', by linarith, hF, hO⟩)
    (by
      intro i σ o hi hσ ho
      obtain ⟨hlev, hc, hiv, htA, has, hs⟩ := hσ
      obtain ⟨hsuc, -, hF, -⟩ := ho
      have hj : m₀ < n - i := by omega
      have hjn : n - i ≤ n := Nat.sub_le n i
      obtain ⟨h1, h2, h3, h4⟩ := hframe (n - i) σ.G _ σ.a _ o.tp o.Preg hlev hF
      have hr : σ.a + 3 * τ (n - i) ≤ max σ.s (σ.a + 3 * τ (n - i)) := le_max_right _ _
      have hw := restart_wait_le τ τ' hτ n (n - i) (by omega) hjn tS σ.a σ.s has hs
      rw [Nat.sub_add_eq]
      exact ⟨hretlevel (n - i) σ.G o.ext hlev hsuc, h3, h4,
        by show tS ≤ σ.a + 3 * τ (n - i); linarith [hτ (n - i)],
        by show σ.a + 3 * τ (n - i) ≤ o.tp; linarith,
        by show o.tp - tS ≤ _; linarith⟩)
  have hInv : ∀ j, m₀ ≤ j → j ≤ n → RunInv level Cas InvP τ τ' n tS j (σs (n - j)) := by
    intro j hj hjn
    have h := hI (n - j) (by omega)
    rwa [Nat.sub_sub_self hjn] at h
  have hGood : ∀ j, m₀ < j → j ≤ n →
      RunGood Succ ret Frame Outp τ τ' tf j (σs (n - j)) (os (n - j)) := by
    intro j hj hjn
    have h := hG (n - j) (by omega)
    rwa [Nat.sub_sub_self hjn] at h
  have hNext : ∀ j, m₀ < j → j ≤ n →
      σs (n - (j - 1)) = runNext ret τ j (σs (n - j)) (os (n - j)) := by
    intro j hj hjn
    have h := hσs (n - j)
    rw [Nat.sub_sub_self hjn] at h
    have he : n - (j - 1) = n - j + 1 := by omega
    rw [he]
    exact h
  refine ⟨fun j => (σs (n - j)).G, fun j => (os (n - j)).ext, fun j => (σs (n - j)).a,
    fun j => (σs (n - j)).s, fun j => (os (n - j)).tp, fun j => (os (n - j)).Preg, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · show (σs (n - n)).G = seed
    rw [Nat.sub_self, hσ0]
  · show (σs (n - n)).a = tS
    rw [Nat.sub_self, hσ0]
  · show (σs (n - n)).s = tS
    rw [Nat.sub_self, hσ0]
  · have h := (hInv m₀ le_rfl hm₀.le).2.2.2.2.2
    show (σs (n - m₀)).s ≤ tS + t₀
    linarith
  · intro j hj hjn
    obtain ⟨hlev, hc, hiv, -, has, hs⟩ := hInv j hj hjn
    exact ⟨hlev, hc, hiv, has, hs⟩
  · intro j hj hjn
    obtain ⟨hsuc, hwn, hF, hO⟩ := hGood j hj hjn
    have hN := hNext j hj hjn
    refine ⟨hsuc, ?_, ?_, ?_, hwn, ?_, ?_⟩
    · show (σs (n - (j - 1))).G = _
      rw [hN]
      rfl
    · show (σs (n - (j - 1))).a = _
      rw [hN]
      rfl
    · show (σs (n - (j - 1))).s = _
      rw [hN]
      rfl
    · show Frame (σs (n - j)).G (σs (n - (j - 1))).G j _ _ _ _
      rw [hN]
      exact hF
    · show Outp (σs (n - j)).G (σs (n - (j - 1))).G j _ _ _
      rw [hN]
      exact hO

end Run
end

end AVRegularity.IterationPassage.Cascade
end
