import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Real.Basic

open Finset Function

/-- Theorem: Every sequence of n^2 + 1 distinct real numbers has a subsequence of length n + 1
    that is either strictly increasing or strictly decreasing. -/
theorem exists_long_subsequence (n : ℕ) :
  ∀ (a : Fin (n^2 + 1) → ℝ), Injective a →
  ∃ (s : Fin (n + 1) → Fin (n^2 + 1)), StrictMono s ∧
  ( (∀ i j, i < j → a (s i) < a (s j)) ∨ (∀ i j, i < j → a (s i) > a (s j)) ) := by
  intro a ha
  by_contra h_contra
  -- Interpret the contradiction assumption: no strictly increasing or decreasing subsequence of length n + 1
  have h_no_inc : ¬ ∃ s : Fin (n + 1) → Fin (n^2 + 1), StrictMono s ∧ ∀ i j, i < j → a (s i) < a (s j) := by
    intro h
    apply h_contra
    obtain ⟨s, hs_mono, hs_inc⟩ := h
    exact ⟨s, hs_mono, Or.inl hs_inc⟩
  have h_no_dec : ¬ ∃ s : Fin (n + 1) → Fin (n^2 + 1), StrictMono s ∧ ∀ i j, i < j → a (s i) > a (s j) := by
    intro h
    apply h_contra
    obtain ⟨s, hs_mono, hs_dec⟩ := h
    exact ⟨s, hs_mono, Or.inr hs_dec⟩

  -- Define the set of lengths of increasing subsequences starting at k
  let L (k : Fin (n^2 + 1)) : Finset ℕ :=
    filter (λ l => ∃ s : Fin l → Fin (n^2 + 1), s 0 = k ∧ StrictMono s ∧
                   ∀ i : Fin (l - 1), a (s (Fin.castSucc i)) < a (s (Fin.succ i))) (range (n^2 + 2))

  -- Prove that L k is nonempty (length 1 is always possible)
  have h_L_nonempty (k : Fin (n^2 + 1)) : L k ≠ ∅ := by
    use 1
    simp [L, mem_filter, mem_range]
    constructor
    · exact Nat.one_le_succ (n^2 + 1)
    · use λ _ => k
      constructor
      · rfl
      · constructor
        · intro i j h
          have : i = j := Fin.ext (by linarith [Fin.val_lt_of_lt h, Fin.val_zero j])
          contradiction
        · intro i
          have hi : i < 0 := by simpa using i
          linarith [Fin.not_lt_zero i hi]

  -- Define i k as the maximum length of an increasing subsequence starting at k
  let i (k : Fin (n^2 + 1)) : ℕ := max' (L k) (h_L_nonempty k)

  -- Define the set of lengths of decreasing subsequences starting at k
  let D (k : Fin (n^2 + 1)) : Finset ℕ :=
    filter (λ l => ∃ s : Fin l → Fin (n^2 + 1), s 0 = k ∧ StrictMono s ∧
                   ∀ i : Fin (l - 1), a (s (Fin.castSucc i)) > a (s (Fin.succ i))) (range (n^2 + 2))

  -- Prove that D k is nonempty
  have h_D_nonempty (k : Fin (n^2 + 1)) : D k ≠ ∅ := by
    use 1
    simp [D, mem_filter, mem_range]
    constructor
    · exact Nat.one_le_succ (n^2 + 1)
    · use λ _ => k
      constructor
      · rfl
      · constructor
        · intro i j h
          have : i = j := Fin.ext (by linarith [Fin.val_lt_of_lt h, Fin.val_zero j])
          contradiction
        · intro i
          have hi : i < 0 := by simpa using i
          linarith [Fin.not_lt_zero i hi]

  -- Define d k as the maximum length of a decreasing subsequence starting at k
  let d (k : Fin (n^2 + 1)) : ℕ := max' (D k) (h_D_nonempty k)

  -- Prove that i k ≤ n
  have h_i_le_n (k : Fin (n^2 + 1)) : i k ≤ n := by
    by_contra h
    have h_i_gt : i k > n := Nat.lt_of_not_le h
    have h_i_mem : i k ∈ L k := max'_mem (L k) (h_L_nonempty k)
    simp [L, mem_filter] at h_i_mem
    obtain ⟨_, ⟨s, hs0, hs_mono, hs_inc⟩⟩ := h_i_mem
    have h_i_ge : i k ≥ n + 1 := Nat.le_of_lt h_i_gt
    let t : Fin (n + 1) → Fin (n^2 + 1) := λ j => s (Fin.castLe h_i_ge j)
    have ht_mono : StrictMono t := by
      intro i j hij
      apply hs_mono
      apply Fin.castLe_lt_of_lt h_i_ge hij
    have ht_inc : ∀ i : Fin (i k₂), a (t (Fin.castSucc i)) < a (t (Fin.succ i)) := by
      intro i
      simp [t]
      split_ifs with h_cast h_succ
      · have : i = 0 := Fin.ext (by simpa [Fin.castSucc] using h_cast)
        simp [this, hs0]
        exact h_a_lt
      · have : i = 0 := Fin.ext (by simpa [Fin.castSucc] using h_cast)
        simp [this, hs0]
        have : Fin.pred (Fin.succ 0) h_succ = 0 := by simp
        rw [this]
        exact h_a_lt
      · have h_succ_ne : Fin.succ i ≠ 0 := by intro h; simp [h] at h_succ
        -- Use cast to align types
        have h_le : (l - 1) + 1 ≤ l := by simp
        exact hs_inc (Fin.cast h_le i)
    have : ∃ s : Fin (n + 1) → Fin (n^2 + 1), StrictMono s ∧ ∀ i j, i < j → a (s i) < a (s j) :=
      ⟨t, ht_mono, ht_inc⟩
    contradiction

  -- Prove that d k ≤ n
  have h_d_le_n (k : Fin (n^2 + 1)) : d k ≤ n := by
    by_contra h
    have h_d_gt : d k > n := Nat.lt_of_not_le h
    have h_d_mem : d k ∈ D k := max'_mem (D k) (h_D_nonempty k)
    simp [D, mem_filter] at h_d_mem
    obtain ⟨_, ⟨s, hs0, hs_mono, hs_dec⟩⟩ := h_d_mem
    have h_d_ge : d k ≥ n + 1 := Nat.le_of_lt h_d_gt
    let t : Fin (n + 1) → Fin (n^2 + 1) := λ j => s (Fin.castLe h_d_ge j)
    have ht_mono : StrictMono t := by
      intro i j hij
      apply hs_mono
      apply Fin.castLe_lt_of_lt h_d_ge hij
    have ht_dec : ∀ i j, i < j → a (t i) > a (t j) := by
      intro i j hij
      have : a (s (Fin.castLe h_d_ge i)) > a (s (Fin.castLe h_d_ge j)) := by
        induction' j using Fin.induction_on with j' ih
        · linarith [Fin.not_lt_zero i hij]
        · cases' lt_or_eq_of_le (Nat.le_of_succ_le (Fin.val_lt_of_lt hij)) with hlt heq
          · have : Fin.castSucc i < Fin.castLe h_d_ge j' := by
              simpa [Fin.castSucc, Fin.castLe] using hlt
            have hi' : Fin.castSucc i < Fin.castLe h_d_ge j' := this
            have hbound : Fin.castSucc i < Fin.castLe h_d_ge j' := hi'
            exact hs_dec ⟨Fin.castSucc i, by simpa using hbound⟩
          · simp [heq, Fin.castSucc, Fin.castLe] at *
      simpa using this
    have : ∃ s : Fin (n + 1) → Fin (n^2 + 1), StrictMono s ∧ ∀ i j, i < j → a (s i) > a (s j) :=
      ⟨t, ht_mono, ht_dec⟩
    contradiction

  -- Define the function f mapping each k to the pair (i k, d k)
  let f : Fin (n^2 + 1) → ℕ × ℕ := λ k => (i k, d k)

  -- Use the pigeonhole principle: since |Fin (n^2 + 1)| = n^2 + 1 > n^2, and (i k, d k) ∈ {1, ..., n} × {1, ..., n},
  -- there exist distinct k₁, k₂ with f k₁ = f k₂
  have h_card_domain : card (univ : Finset (Fin (n^2 + 1))) = n^2 + 1 := by simp
  have h_card_image : (univ.map ⟨f, λ _ _ => rfl⟩).card ≤ n^2 := by
    apply card_le_of_subset
    intro x hx
    simp [mem_map] at hx
    obtain ⟨k, _, hfk⟩ := hx
    subst hfk
    simp [mem_product, mem_Ico]
    exact ⟨Nat.one_le_max' _ (h_L_nonempty k), h_i_le_n k, Nat.one_le_max' _ (h_D_nonempty k), h_d_le_n k⟩
  have h_card_lt : n^2 < card (univ : Finset (Fin (n^2 + 1))) := by simp [h_card_domain]
  have h_exists : ∃ k₁ k₂, k₁ ≠ k₂ ∧ f k₁ = f k₂ := by
    have : ¬ Injective f := by
      intro h_inj
      have h_eq : (univ.map ⟨f, λ _ _ => rfl⟩).card = univ.card := card_map ⟨f, h_inj⟩
      rw [h_card_domain] at h_eq
      have : n^2 + 1 ≤ n^2 := h_eq.trans h_card_image
      linarith
    rwa [not_injective_iff] at this

  -- Extract distinct k₁, k₂ and ensure k₁ < k₂
  obtain ⟨k₁, k₂, h_ne, h_eq⟩ := h_exists
  wlog h_k_lt : k₁ < k₂ generalizing k₁ k₂
  · exact this k₂ k₁ h_eq h_ne.symm (h_ne.symm.lt_or_lt.resolve_right h_k_lt)

  -- Extract equality of pairs
  have h_i_eq : i k₁ = i k₂ := (Prod.mk.inj_iff.mp h_eq).1
  have h_d_eq : d k₁ = d k₂ := (Prod.mk.inj_iff.mp h_eq).2

  -- Since a is injective, a k₁ ≠ a k₂, so either a k₁ < a k₂ or a k₂ < a k₁
  cases lt_or_gt_of_ne (ha.ne h_ne) with
  | inl h_a_lt =>
    -- Case: a k₁ < a k₂
    have h_i_k₂_mem : i k₂ ∈ L k₂ := max'_mem (L k₂) (h_L_nonempty k₂)
    simp [L, mem_filter] at h_i_k₂_mem
    obtain ⟨_, ⟨s, hs0, hs_mono, hs_inc⟩⟩ := h_i_k₂_mem
    let t : Fin (i k₂ + 1) → Fin (n^2 + 1) := λ j => if h : j = 0 then k₁ else s (Fin.pred j h)
    have ht_mono : StrictMono t := by
      intro i j hij
      simp [t]
      split_ifs with hi hj
      · contradiction
      · have : Fin.pred j hj = 0 := by
          have : j = 1 := Fin.ext (by linarith [Fin.val_lt_of_lt hij, Fin.val_zero i])
          simp [this]
        rw [hs0, this]
        exact h_k_lt
      · exact h_k_lt
      · apply hs_mono
        apply Fin.pred_lt_pred hij
        · intro h
          simp [h] at hj
        · intro h
          simp [h] at hi
    have ht_inc : ∀ i : Fin (i k₂), a (t (Fin.castSucc i)) < a (t (Fin.succ i)) := by
      intro i
      simp [t]
      split_ifs with h_cast h_succ
      · have : i = 0 := Fin.ext (by simpa [Fin.castSucc] using h_cast)
        simp [this, hs0]
        exact h_a_lt
      · have : i = 0 := Fin.ext (by simpa [Fin.castSucc] using h_cast)
        simp [this, hs0]
        have : Fin.pred (Fin.succ 0) h_succ = 0 := by simp
        rw [this]
        exact h_a_lt
      · have h_succ_ne : Fin.succ i ≠ 0 := by intro h; simp [h] at h_succ
        exact hs_inc (Fin.castSucc i)
    have h_t_in_L : i k₂ + 1 ∈ L k₁ := by
      simp [L, mem_filter, mem_range]
      constructor
      · exact Nat.le_succ_of_le (Nat.le_of_lt_succ k₁.isLt)
      · use t
        exact ⟨rfl, ht_mono, ht_inc⟩
    have h_i_k₁_ge : i k₁ ≥ i k₂ + 1 := le_max' (L k₁) (h_L_nonempty k₁) _ h_t_in_L
    rw [h_i_eq] at h_i_k₁_ge
    linarith
  | inr h_a_gt =>
    -- Case: a k₁ > a k₂
    have h_d_k₂_mem : d k₂ ∈ D k₂ := max'_mem (D k₂) (h_D_nonempty k₂)
    simp [D, mem_filter] at h_d_k₂_mem
    obtain ⟨_, ⟨s, hs0, hs_mono, hs_dec⟩⟩ := h_d_k₂_mem
    let t : Fin (d k₂ + 1) → Fin (n^2 + 1) := λ j => if h : j = 0 then k₁ else s (Fin.pred j h)
    have ht_mono : StrictMono t := by
      intro i j hij
      simp [t]
      split_ifs with hi hj
      · contradiction
      · have : Fin.pred j hj = 0 := by
          have : j = 1 := Fin.ext (by linarith [Fin.val_lt_of_lt hij, Fin.val_zero i])
          simp [this]
        rw [hs0, this]
        exact h_k_lt
      · exact h_k_lt
      · apply hs_mono
        apply Fin.pred_lt_pred hij
        · intro h
          simp [h] at hj
        · intro h
          simp [h] at hi
    have ht_dec : ∀ i : Fin (d k₂), a (t (Fin.castSucc i)) > a (t (Fin.succ i)) := by
      intro i
      simp [t]
      split_ifs with h_cast h_succ
      · have : i = 0 := Fin.ext (by simpa [Fin.castSucc] using h_cast)
        simp [this, hs0]
        exact h_a_gt
      · have : i = 0 := Fin.ext (by simpa [Fin.castSucc] using h_cast)
        simp [this, hs0]
        have : Fin.pred (Fin.succ 0) h_succ = 0 := by simp
        rw [this]
        exact h_a_gt
      · have h_succ_ne : Fin.succ i ≠ 0 := by intro h; simp [h] at h_succ
        exact hs_dec (Fin.castSucc i)
    have h_t_in_D : d k₂ + 1 ∈ D k₁ := by
      simp [D, mem_filter, mem_range]
      constructor
      · exact Nat.le_succ_of_le (Nat.le_of_lt_succ k₁.isLt)
      · use t
        exact ⟨rfl, ht_mono, ht_dec⟩
    have h_d_k₁_ge : d k₁ ≥ d k₂ + 1 := le_max' (D k₁) (h_D_nonempty k₁) _ h_t_in_D
    rw [h_d_eq] at h_d_k₁_ge
    linarith
