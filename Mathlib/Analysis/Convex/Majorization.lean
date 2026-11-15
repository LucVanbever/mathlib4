/-
Copyright (c) 2026 Luc Vanbever. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luc Vanbever
-/
module

public import Mathlib.Analysis.Convex.DoublyStochasticMatrix

import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

/-!
# Majorization

## Main definitions

* `MajorizedBy x y`: any `k` entries of `x` sum to at most
  some `k` entries of `y`, and the totals agree.

## Main statements

* `majorizedBy_iff_exists_doublyStochastic`: `x` is majorized by `y` iff `x = M *ᵥ y` for a
  doubly stochastic matrix `M`.

## Implementation notes

`MajorizedBy` is stated without sorting, so it makes sense for vectors indexed by an arbitrary
finite type `ι`. The usual definition compares the sums of the `k` largest entries, which
requires a choice of ordering and a choice of tie-breaking. The two definitions agree because
the largest sum of `k` entries of a vector is the sum of its `k` largest entries.

To show that `x = M *ᵥ y` for some doubly stochastic `M` when `x` is majorized by `y`, we follow
the classical argument of Hardy, Littlewood and Pólya, as presented in [MarshallOlkinArnold2011].
Both vectors are first reindexed by `Fin (Fintype.card ι)` so that they become antitone
(`exists_equiv_antitone_comp`). For antitone vectors, `y` is moved towards `x` by a finite
sequence of transfer steps (T-transforms), each of which replaces `y` by `T *ᵥ y` for a doubly
stochastic matrix `T`. The number of coordinates where `y` differs from `x` decreases at each
step, so the product of the matrices `T` gives the required `M`. The matrix is then transported
back to `ι` via the reindexing (with `Matrix.reindex` and `reindex_mem_doublyStochastic`).

For the converse, Birkhoff's theorem writes `M` as a convex combination of permutation
matrices. Each permutation matrix only rearranges `y`, and the sum of a rearrangement of `y`
over a set of size `k` is at most the largest such sum of `y`.

## References

* [A. W. Marshall, I. Olkin, B. C. Arnold, *Inequalities: Theory of Majorization and Its
Applications*][MarshallOlkinArnold2011]

## Tags

majorization, doubly stochastic
-/

@[expose] public section

open Finset Matrix

section Defs

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid R] [LE R]

/-- `x` is majorized by `y`: any `k` entries of `x` sum to at most some `k` entries of `y`,
and the totals agree. This is equivalent to the usual definition via the sums of the `k`
largest entries. -/
def MajorizedBy (x y : ι → R) : Prop :=
  (∀ S : Finset ι, ∃ T : Finset ι, T.card = S.card ∧ ∑ i ∈ S, x i ≤ ∑ i ∈ T, y i) ∧
    ∑ i, x i = ∑ i, y i

/-- Majorization is invariant under reindexing: if `x` is majorized by `y`, then `x ∘ φ` is
majorized by `y ∘ ψ` for any two equivalences `φ ψ : κ ≃ ι`. The two vectors may be
reindexed independently. -/
theorem MajorizedBy.comp_equiv {x y : ι → R} (h : MajorizedBy x y) (φ ψ : κ ≃ ι) :
    MajorizedBy (x ∘ φ) (y ∘ ψ) := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨fun S => ?_, ?_⟩
  · obtain ⟨T, hT, hle⟩ := h₁ (S.map φ.toEmbedding)
    refine ⟨T.map ψ.symm.toEmbedding, ?_, ?_⟩
    · rw [Finset.card_map, hT, Finset.card_map]
    · simpa [Finset.sum_map] using hle
  · simp only [Function.comp_apply]
    rw [Equiv.sum_comp φ x, Equiv.sum_comp ψ y]
    exact h₂

end Defs

section Sorting

variable {ι R : Type*} [Fintype ι] [LinearOrder R]

/-- Every vector can be reindexed by an equivalence with `Fin (Fintype.card ι)` so
that it becomes antitone. -/
theorem exists_equiv_antitone_comp (x : ι → R) :
    ∃ φ : Fin (Fintype.card ι) ≃ ι, Antitone (x ∘ φ) := by
  let e := Fintype.equivFin ι
  let f : Fin (Fintype.card ι) → Rᵒᵈ := fun i => OrderDual.toDual (x (e.symm i))
  refine ⟨(Tuple.sort f).trans e.symm, fun a b hab => ?_⟩
  have h := Tuple.monotone_sort f hab
  simpa [f] using h

end Sorting

section InitialSegm

variable {n : ℕ}

/-- The initial segment of `Fin n` containing all elements strictly less than `m`. -/
private def initialSegm (m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i : ℕ) < m)

/-- `i` belongs to the initial segment `initialSegm m` of `Fin n` iff its value is below `m`. -/
private lemma mem_initialSegm {m : ℕ} {i : Fin n} :
    i ∈ (initialSegm m : Finset (Fin n)) ↔ (i : ℕ) < m := by
  simp only [initialSegm, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The initial segment `initialSegm m` of `Fin n` has `m` elements, provided `m ≤ n`. -/
private lemma card_initialSegm {m : ℕ} (hm : m ≤ n) :
    (initialSegm m : Finset (Fin n)).card = m := by
  have : (initialSegm m : Finset (Fin n)) =
      (Finset.univ : Finset (Fin m)).map (Fin.castLEEmb hm) := by
    ext i
    simp only [initialSegm, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro h; exact ⟨⟨i, h⟩, rfl⟩
    · rintro ⟨a, rfl⟩; simp
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Extending the initial segment from `k` to `k + 1` adds exactly the term at index `k`:
the sum of `F` over the first `k + 1` indices is the sum over the first `k` plus `F k`. -/
private lemma sum_initialSegm_succ {R : Type*} [AddCommMonoid R] (F : Fin n → R) (k : Fin n) :
    ∑ i ∈ initialSegm ((k : ℕ) + 1), F i = ∑ i ∈ initialSegm (k : ℕ), F i + F k := by
  have hsplit : (initialSegm ((k : ℕ) + 1) : Finset (Fin n)) = insert k (initialSegm (k : ℕ)) := by
    ext i
    simp only [initialSegm, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases h : i = k
      · exact Or.inl h
      · right
        have : (i : ℕ) ≠ k := fun h' => h (Fin.ext h')
        omega
    · rintro (rfl | hi) <;> omega
  have hk : k ∉ (initialSegm (k : ℕ) : Finset (Fin n)) := by
    unfold initialSegm
    rw [Finset.mem_filter]
    intro h
    exact lt_irrefl k.val h.2
  rw [hsplit, Finset.sum_insert hk, add_comm]

end InitialSegm

section Sorted

variable {n : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Exchange argument: an antitone `w` is maximised on `initialSegm m`
among all subsets of size `m`. -/
private lemma sum_le_sum_initialSegm {w : Fin n → R} (hw : Antitone w) {m : ℕ}
    (S : Finset (Fin n)) (hS : S.card = m) :
    ∑ i ∈ S, w i ≤ ∑ i ∈ initialSegm m, w i := by
  have hm : m ≤ n := by
    have := Finset.card_le_univ S
    simpa [hS] using this
  set L : Finset (Fin n) := initialSegm m
  have hLcard : L.card = m := card_initialSegm hm
  -- `S \ L` and `L \ S` have the same size
  have hcard : (S \ L).card = (L \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S L
    have h2 := Finset.card_sdiff_add_card_inter L S
    rw [Finset.inter_comm] at h2
    omega
  -- the elements of `L \ S` are worth at least as much as those of `S \ L`
  have key : ∑ i ∈ S \ L, w i ≤ ∑ i ∈ L \ S, w i := by
    by_cases hB : (L \ S).Nonempty
    · -- pivot: the smallest value of `w` on `L \ S`
      obtain ⟨j, hj, hjmin⟩ := Finset.exists_min_image (L \ S) w hB
      have hjL : j ∈ L := (Finset.mem_sdiff.mp hj).1
      calc ∑ i ∈ S \ L, w i ≤ (S \ L).card • w j := by
            apply Finset.sum_le_card_nsmul
            intro i hi
            have hiL : i ∉ L := (Finset.mem_sdiff.mp hi).2
            have hj_lt : (j : ℕ) < m := mem_initialSegm.mp hjL
            have hi_ge : ¬ (i : ℕ) < m := fun h => hiL (mem_initialSegm.mpr h)
            have hlt : j < i := Fin.lt_def.mpr (by omega)
            exact hw hlt.le
        _ = (L \ S).card • w j := by rw [hcard]
        _ ≤ ∑ i ∈ L \ S, w i := Finset.card_nsmul_le_sum _ _ _ hjmin
    · -- `L \ S` is empty, so `S \ L` is empty too
      have hB' : L \ S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
      have hA : S \ L = ∅ := Finset.card_eq_zero.mp (by simp [hcard, hB'])
      rw [hA, hB']
  -- the common part `S ∩ L` cancels
  have h1 := Finset.sum_inter_add_sum_sdiff S L w
  have h2 := Finset.sum_inter_add_sum_sdiff L S w
  rw [Finset.inter_comm] at h2
  rw [← h1, ← h2, add_le_add_iff_left]
  exact key

/-- For antitone `y`, majorization gives the usual partial-sum inequalities. -/
private lemma MajorizedBy.sum_initialSegm_le {x y : Fin n → R} (h : MajorizedBy x y)
    (hy : Antitone y) {m : ℕ} (hm : m ≤ n) :
    ∑ i ∈ initialSegm m, x i ≤ ∑ i ∈ initialSegm m, y i := by
  obtain ⟨T, hT, hle⟩ := h.1 (initialSegm m)
  rw [card_initialSegm hm] at hT
  exact hle.trans (sum_le_sum_initialSegm hy T hT)

/-- Conversely, for antitone `x`, the partial-sum inequalities give majorization. -/
private lemma majorizedBy_of_sum_initialSegm_le {x y : Fin n → R} (hx : Antitone x)
    (hP : ∀ m ≤ n, ∑ i ∈ initialSegm m, x i ≤ ∑ i ∈ initialSegm m, y i)
    (htot : ∑ i, x i = ∑ i, y i) : MajorizedBy x y := by
  refine ⟨fun S => ?_, htot⟩
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  exact ⟨initialSegm S.card, card_initialSegm hS,
    (sum_le_sum_initialSegm hx S rfl).trans (hP S.card hS)⟩

/-- Indices for one transfer step. If `y` is antitone, `x` is majorized by `y` and `x ≠ y`,
there are indices `j < k` with `x j < y j`, `y k < x k` and `x i = y i` for `j < i < k`, and
`x i ≤ y i` for all `i < k`. Moving a small amount from coordinate `j` to coordinate `k` of `y`
brings it closer to `x` (see `exists_doublyStochastic_step`). -/
private lemma exists_transfer_jk_indices {x y : Fin n → R} (hy : Antitone y)
    (h : MajorizedBy x y) (hne : x ≠ y) :
    ∃ j k : Fin n, j < k ∧ x j < y j ∧ y k < x k ∧
     (∀ i, j < i → i < k → x i = y i) ∧ ∀ i, i < k → x i ≤ y i := by
  -- partial sums of `x` are bounded by those of `y`
  have hP : ∀ m ≤ n, ∑ i ∈ initialSegm m, x i ≤ ∑ i ∈ initialSegm m, y i :=
    fun m hm => h.sum_initialSegm_le hy hm
  -- some coordinate has `y i < x i`
  have hex : ∃ i, y i < x i := by
    by_contra hcon
    push Not at hcon
    apply hne
    funext i
    exact (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => hcon i)).mp h.2
      i (Finset.mem_univ i)
  obtain ⟨i0, hi0⟩ := hex
  -- `k` : the first such coordinate
  obtain ⟨k, hk, hkmin⟩ :=
    (wellFounded_lt : WellFounded ((· < ·) : Fin n → Fin n → Prop)).has_min
      {i | y i < x i} ⟨i0, hi0⟩
  have hk' : y k < x k := hk
  have hbefore : ∀ i, i < k → x i ≤ y i :=
    fun i hi => not_lt.mp (fun hlt => hkmin i hlt hi)
  -- some coordinate below `k` has `x i < y i`
  have hexj : ∃ i, i < k ∧ x i < y i := by
    by_contra hcon
    push Not at hcon
    have heq : ∀ i, i < k → x i = y i :=
      fun i hi => le_antisymm (hbefore i hi) (hcon i hi)
    have hk1 : (k : ℕ) + 1 ≤ n := by have := k.isLt; omega
    have hle := hP ((k : ℕ) + 1) hk1
    rw [sum_initialSegm_succ x k, sum_initialSegm_succ y k] at hle
    have hsum : ∑ i ∈ initialSegm (k : ℕ), x i = ∑ i ∈ initialSegm (k : ℕ), y i :=
      Finset.sum_congr rfl (fun i hi => heq i (by simpa [initialSegm] using hi))
    rw [hsum] at hle
    have h_cancel : x k ≤ y k := (add_le_add_iff_left (∑ i ∈ initialSegm ↑k, y i)).mp hle
    exact (not_le_of_gt hk') h_cancel
  -- `j` : the last such coordinate
  set s : Finset (Fin n) := Finset.univ.filter (fun i => i < k ∧ x i < y i) with hs
  have hmem : ∀ i, i ∈ s ↔ i < k ∧ x i < y i := by intro i; simp [hs]
  obtain ⟨i1, hi1⟩ := hexj
  have hsne : s.Nonempty := ⟨i1, (hmem i1).mpr hi1⟩
  have hjmem := (hmem _).mp (Finset.max'_mem s hsne)
  refine ⟨s.max' hsne, k, hjmem.1, hjmem.2, hk', ?_, hbefore⟩
  intro i hji hik
  apply le_antisymm (hbefore i hik)
  by_contra hlt
  push Not at hlt
  have hi : i ∈ s := (hmem i).mpr ⟨hik, hlt⟩
  exact lt_irrefl _ (lt_of_lt_of_le hji (Finset.le_max' s i hi))

/-- One T-transform step. If `x` and `y` are antitone, `x` is majorized by `y`, and `x ≠ y`,
then there is a doubly stochastic matrix `T` (a convex combination of the identity and a
transposition) such that `y' = T *ᵥ y` is still antitone, still majorizes `x`, and
differs from `x` in strictly fewer coordinates than `y` does. -/
private lemma exists_doublyStochastic_step {x y : Fin n → R} (hx : Antitone x) (hy : Antitone y)
    (h : MajorizedBy x y) (hne : x ≠ y) :
    ∃ (T : Matrix (Fin n) (Fin n) R) (y' : Fin n → R),
      T ∈ doublyStochastic R (Fin n) ∧ T *ᵥ y = y' ∧
      Antitone y' ∧ MajorizedBy x y' ∧
      (Finset.univ.filter (fun i => y' i ≠ x i)).card <
        (Finset.univ.filter (fun i => y i ≠ x i)).card := by
  obtain ⟨j, k, hjk, hxj, hyk, hmid, hbef⟩ := exists_transfer_jk_indices hy h hne
  have htot : ∑ i, x i = ∑ i, y i := h.2
  have hjk_ne : j ≠ k := hjk.ne
  -- case split on whether i is j, k, or neither
  have cls : ∀ i : Fin n, i = j ∨ i = k ∨ (i ≠ j ∧ i ≠ k) := by
    intro i
    by_cases h1 : i = j
    · exact Or.inl h1
    · by_cases h2 : i = k
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
  -- the amount `δ` moved from coordinate `j` to coordinate `k`
  obtain ⟨δ, hδa, hδb, hδpos, hδc⟩ : ∃ δ : R, δ ≤ y j - x j ∧ δ ≤ x k - y k ∧ 0 < δ ∧
      (δ = y j - x j ∨ δ = x k - y k) :=
    ⟨min (y j - x j) (x k - y k), min_le_left _ _, min_le_right _ _,
      lt_min (sub_pos.mpr hxj) (sub_pos.mpr hyk), min_choice _ _⟩
  -- the new vector, described only through the facts we need
  obtain ⟨y', hy'j, hy'k, hy'o, hsumS⟩ : ∃ y' : Fin n → R,
      y' j = y j - δ ∧ y' k = y k + δ ∧ (∀ i, i ≠ j → i ≠ k → y' i = y i) ∧
      ∀ S : Finset (Fin n), ∑ i ∈ S, y' i =
        ∑ i ∈ S, y i + (if k ∈ S then δ else 0) - (if j ∈ S then δ else 0) := by
    refine ⟨fun i => y i + (if i = k then δ else 0) - (if i = j then δ else 0),
      ?_, ?_, ?_, ?_⟩
    · simp [hjk_ne]
    · simp [hjk_ne.symm]
    · intro i hij hik; simp [hij, hik]
    · intro S; simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- the T-transform matrix
  have hpos : 0 < y j - y k := by linarith [hx hjk.le]
  obtain ⟨lam, hlam0, hlam1, hlam⟩ : ∃ lam : R, 0 ≤ lam ∧ lam ≤ 1 ∧ lam * (y j - y k) = δ := by
    refine ⟨δ / (y j - y k), div_nonneg hδpos.le hpos.le,
      (div_le_one hpos).mpr (by linarith [hx hjk.le]), ?_⟩
    have := hpos.ne'
    field_simp
  have hperm : ∀ i, ∀ lam : R, ((lam • Equiv.Perm.permMatrix R (Equiv.swap j k)) *ᵥ y) i
                                = lam * y (Equiv.swap j k i) := by
    intro i
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.mulVec, dotProduct]
  obtain ⟨T, hmem, hT⟩ : ∃ T ∈ doublyStochastic R (Fin n), T *ᵥ y = y' := by
    refine ⟨(1 - lam) • (1 : Matrix (Fin n) (Fin n) R)
        + lam • Equiv.Perm.permMatrix R (Equiv.swap j k), ?_, ?_⟩
    · exact convex_doublyStochastic (doublyStochastic R (Fin n)).one_mem
        permMatrix_mem_doublyStochastic (sub_nonneg.mpr hlam1) hlam0 (sub_add_cancel 1 lam)
    · funext i
      have e : (((1 - lam) • (1 : Matrix (Fin n) (Fin n) R)
          + lam • Equiv.Perm.permMatrix R (Equiv.swap j k)) *ᵥ y) i
          = (1 - lam) * y i + lam * y (Equiv.swap j k i) := by
        simp only [add_mulVec, Pi.add_apply, hperm, add_left_inj]
        simp [Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [e]
      rcases cls i with hp | hp | ⟨hij, hik⟩
      · rw [hp, hy'j, Equiv.swap_apply_left]; linarith [hlam]
      · rw [hp, hy'k, Equiv.swap_apply_right]; linarith [hlam]
      · rw [hy'o i hij hik, Equiv.swap_apply_of_ne_of_ne hij hik]; ring
  -- `y'` is antitone
  have hanti : Antitone y' := by
    intro p q hpq
    rcases cls p with hp | hp | ⟨hpj, hpk⟩ <;> rcases cls q with hq | hq | ⟨hqj, hqk⟩
    · exact le_of_eq (by rw [hp, hq])
    · rw [hp, hq, hy'j, hy'k]; linarith [hx hjk.le]
    · have hjq : j ≤ q := by rw [← hp]; exact hpq
      have hjq' : j < q := lt_of_le_of_ne hjq hqj.symm
      rw [hp, hy'j, hy'o q hqj hqk]
      rcases lt_or_gt_of_ne hqk with hqk' | hqk'
      · linarith [hmid q hjq' hqk', hx hjq, hx hjq'.le]
      · linarith [hy hqk'.le, hx hjk.le]
    · rw [hp, hq] at hpq; exact absurd hjk (not_lt.mpr hpq)
    · exact le_of_eq (by rw [hp, hq])
    · have hkq : k ≤ q := by rw [← hp]; exact hpq
      rw [hp, hy'k, hy'o q hqj hqk]
      linarith [hy hkq]
    · have hpj' : p ≤ j := by rw [← hq]; exact hpq
      rw [hq, hy'j, hy'o p hpj hpk]
      linarith [hy hpj']
    · have hpk' : p ≤ k := by rw [← hq]; exact hpq
      have hpk'' : p < k := lt_of_le_of_ne hpk' hpk
      rw [hq, hy'k, hy'o p hpj hpk]
      rcases lt_or_gt_of_ne hpj with hpj' | hpj'
      · linarith [hy hpj'.le, hx hjk.le]
      · linarith [hmid p hpj' hpk'', hx hpk''.le]
    · rw [hy'o q hqj hqk, hy'o p hpj hpk]; exact hy hpq
  -- `y'` still majorizes `x`
  have hPy : ∀ m ≤ n, ∑ i ∈ (initialSegm m : Finset (Fin n)), x i ≤ ∑ i ∈ initialSegm m, y i :=
    fun m hm => h.sum_initialSegm_le hy hm
  have hmaj' : MajorizedBy x y' := by
    refine majorizedBy_of_sum_initialSegm_le hx (fun m hm => ?_) ?_
    · rw [hsumS (initialSegm m)]
      have hP := hPy m hm
      by_cases hjm : j ∈ (initialSegm m : Finset (Fin n))
      · by_cases hkm : k ∈ (initialSegm m : Finset (Fin n))
        · rw [ite_eq_left hkm, ite_eq_left hjm]; linarith
        · have hmk : m ≤ (k : ℕ) := not_lt.mp (fun h => hkm (mem_initialSegm.mpr h))
          have key : y j - x j ≤ ∑ i ∈ (initialSegm m : Finset (Fin n)), (y i - x i) :=
            Finset.single_le_sum (f := fun i => y i - x i)
              (fun i hi => sub_nonneg.mpr
                (hbef i (Fin.lt_def.mpr (lt_of_lt_of_le (mem_initialSegm.mp hi) hmk)))) hjm
          rw [Finset.sum_sub_distrib] at key
          rw [ite_eq_right hkm, ite_eq_left hjm]; linarith
      · by_cases hkm : k ∈ (initialSegm m : Finset (Fin n))
        · exact absurd (mem_initialSegm.mpr
            (lt_trans (Fin.lt_def.mp hjk) (mem_initialSegm.mp hkm))) hjm
        · rw [ite_eq_right hkm, ite_eq_right hjm]; linarith
    · rw [hsumS Finset.univ, ite_eq_left (Finset.mem_univ k), ite_eq_left (Finset.mem_univ j), htot]
      ring
  -- fewer mismatches
  have hsub : Finset.univ.filter (fun i => y' i ≠ x i) ⊆
      Finset.univ.filter (fun i => y i ≠ x i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rcases cls i with hp | hp | ⟨hij, hik⟩
    · rw [hp]; exact hxj.ne'
    · rw [hp]; exact hyk.ne
    · rwa [hy'o i hij hik] at hi
  have hcard : (Finset.univ.filter (fun i => y' i ≠ x i)).card <
      (Finset.univ.filter (fun i => y i ≠ x i)).card := by
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ?_)
    rcases hδc with hd | hd
    · refine ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hxj.ne'
      · intro hmem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        apply hmem; rw [hy'j]; linarith
    · refine ⟨k, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hyk.ne
      · intro hmem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        apply hmem; rw [hy'k]; linarith
  exact ⟨T, y', hmem, hT, hanti, hmaj', hcard⟩

/-- Sorted case of `exists_doublyStochastic_of_majorizedBy`: if `x` and `y` are antitone and
`x` is majorized by `y`, then `x = M *ᵥ y` for a doubly stochastic `M`. The proof composes
T-transforms, by induction on the number of coordinates where `y` differs from `x`. -/
private theorem exists_doublyStochastic_of_antitone {x y : Fin n → R}
    (hx : Antitone x) (hy : Antitone y) (h : MajorizedBy x y) :
    ∃ M ∈ doublyStochastic R (Fin n), M *ᵥ y = x := by
  -- generalize over `y`, and induct on the number of mismatches with `x`
  suffices H : ∀ c : ℕ, ∀ z : Fin n → R, Antitone z → MajorizedBy x z →
      (Finset.univ.filter (fun i => z i ≠ x i)).card = c →
      ∃ M ∈ doublyStochastic R (Fin n), M *ᵥ z = x from
    H _ y hy h rfl
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro z hz hxz hc
    by_cases hxy : x = z
    · -- nothing to do: `M = 1`
      exact ⟨1, (doublyStochastic R (Fin n)).one_mem, by simp [hxy]⟩
    · -- one T-transform reduces the number of mismatches
      obtain ⟨T, z', hT, hTz, hz', hxz', hlt⟩ := exists_doublyStochastic_step hx hz hxz hxy
      obtain ⟨M, hM, hMz'⟩ := ih _ (lt_of_lt_of_eq hlt hc) z' hz' hxz' rfl
      refine ⟨M * T, (doublyStochastic R (Fin n)).mul_mem hM hT, ?_⟩
      rw [← Matrix.mulVec_mulVec, hTz, hMz']

end Sorted

section Main

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- If `x` is majorized by `y`, then `x = M *ᵥ y` for some doubly stochastic matrix `M`. -/
theorem exists_doublyStochastic_of_majorizedBy {x y : ι → R} (h : MajorizedBy x y) :
    ∃ M ∈ doublyStochastic R ι, M *ᵥ y = x := by
  -- reindex both vectors by `Fin (Fintype.card ι)` so that they become antitone
  obtain ⟨φ, hφ⟩ := exists_equiv_antitone_comp x
  obtain ⟨ψ, hψ⟩ := exists_equiv_antitone_comp y
  -- majorization is preserved by reindexing
  have hmaj : MajorizedBy (x ∘ φ) (y ∘ ψ) := h.comp_equiv φ ψ
  -- the sorted case
  obtain ⟨M, hM, hMy⟩ := exists_doublyStochastic_of_antitone hφ hψ hmaj
  -- transport the matrix back to `ι`
  refine ⟨(reindex φ ψ) M, reindex_mem_doublyStochastic hM, ?_⟩
  funext a
  have h1 := congrFun hMy (φ.symm a)
  simp only [Matrix.mulVec, dotProduct, Function.comp_apply,
    Equiv.apply_symm_apply] at h1
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ b, M (φ.symm a) (ψ.symm b) * y b
      = ∑ b, (fun c => M (φ.symm a) c * y (ψ c)) (ψ.symm b) := by simp
    _ = ∑ c, M (φ.symm a) c * y (ψ c) := ψ.symm.sum_comp (fun c ↦ M (φ.symm a) c * y (ψ c))
    _ = x a := h1

/-- `M *ᵥ y` is majorized by `y` when `M` is doubly stochastic. -/
theorem majorizedBy_mulVec_of_mem_doublyStochastic {M : Matrix ι ι R}
    (hM : M ∈ doublyStochastic R ι) (y : ι → R) : MajorizedBy (M *ᵥ y) y := by
  -- write x for M *ᵥ y
  generalize hx : M *ᵥ y = x
  -- Birkhoff: `M` is a convex combination of permutation matrices
  obtain ⟨w, hw0, hw1, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  -- each permutation matrix rearranges `y`
  have hπ : ∀ σ : Equiv.Perm ι, ∃ π : Equiv.Perm ι,
      ∀ i, (σ.permMatrix R *ᵥ y) i = y (π i) :=
    fun σ => ⟨σ, fun i => by simp [Matrix.permMatrix_mulVec]⟩
  choose π hπ using hπ
  -- `x` is the corresponding convex combination of rearrangements of `y`
  have hxi : ∀ i, x i = ∑ σ, w σ * y (π σ i) := by
    intro i
    have h : x = ∑ σ, w σ • (σ.permMatrix R *ᵥ y) := by
      rw [← hx, ← hwM, Matrix.sum_mulVec]
      simp [Matrix.smul_mulVec]
    rw [h]
    simp [Finset.sum_apply, hπ]
  -- sums over a set `S`
  have hS : ∀ S : Finset ι, ∑ i ∈ S, x i = ∑ σ, w σ * ∑ i ∈ S, y (π σ i) := by
    intro S
    simp_rw [hxi]
    rw [Finset.sum_comm]
    simp [Finset.mul_sum]
  refine ⟨fun S => ?_, ?_⟩
  · -- `T` : a best set of size `|S|` for `y`
    obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image
      (powersetCard S.card (univ : Finset ι)) (fun T => ∑ j ∈ T, y j)
      ⟨S, mem_powersetCard.mpr ⟨subset_univ S, rfl⟩⟩
    refine ⟨T, (mem_powersetCard.mp hT).2, ?_⟩
    rw [hS S]
    calc ∑ σ, w σ * ∑ i ∈ S, y (π σ i)
        ≤ ∑ σ, w σ * ∑ j ∈ T, y j := by
          refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ (hw0 σ)
          -- the rearranged set `S.map (π σ)` also has size `|S|`
          have h := hmax (S.map (π σ).toEmbedding)
            (mem_powersetCard.mpr ⟨subset_univ _, by simp⟩)
          simpa [Finset.sum_map] using h
      _ = ∑ j ∈ T, y j := by rw [← Finset.sum_mul, hw1, one_mul]
  · -- totals: each rearrangement of `y` has the same total
    rw [hS univ]
    calc ∑ σ, w σ * ∑ i, y (π σ i) = ∑ σ, w σ * ∑ i, y i := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Equiv.sum_comp (π σ) y]
      _ = ∑ i, y i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **Majorization via doubly stochastic matrices.**
`x` is majorized by `y` iff `x = M *ᵥ y` for some doubly stochastic matrix `M`. -/
theorem majorizedBy_iff_exists_doublyStochastic {x y : ι → R} :
    MajorizedBy x y ↔ ∃ M ∈ doublyStochastic R ι, M *ᵥ y = x :=
  ⟨exists_doublyStochastic_of_majorizedBy,
    fun ⟨_, hM, hx⟩ => by
      subst hx
      exact majorizedBy_mulVec_of_mem_doublyStochastic hM y⟩

end Main
