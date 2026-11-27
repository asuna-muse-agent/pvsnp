import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_poly_normal

/-
Uses the settled unit PvsNP/Units/m2_p_poly_normal.lean of github.com/makedotfun/pvsnp
(Apache License 2.0): its `polynomial_le_pow_add` bounds a polynomial by `n ^ k + k`.
-/

/-- Evaluating a polynomial at an exponentially bounded function stays exponentially
bounded: the polynomial is at most `(f n) ^ k + k`, and the `+ k` is absorbed by one
more factor of the base. -/
theorem PvsNP.Units.m2_eb_poly :
    ∀ (p : Polynomial ℕ) (f : ℕ → ℕ), (∃ A D : ℕ, ∀ n : ℕ, f n ≤ 2 ^ (A * (n + 1) ^ D)) →
      ∃ A D : ℕ, ∀ n : ℕ, p.eval (f n) ≤ 2 ^ (A * (n + 1) ^ D) := by
  intro p f ⟨A₀, D₀, hf⟩
  obtain ⟨k, hk⟩ := PvsNP.Units.m2_p_poly_normal.polynomial_le_pow_add p
  refine ⟨k * A₀ + k + 1, D₀, fun n => ?_⟩
  have h1 : p.eval (f n) ≤ (f n) ^ k + k := hk (f n)
  have h2 : (f n) ^ k ≤ 2 ^ (k * A₀ * (n + 1) ^ D₀) := by
    calc (f n) ^ k ≤ (2 ^ (A₀ * (n + 1) ^ D₀)) ^ k := Nat.pow_le_pow_left (hf n) k
      _ = 2 ^ (k * A₀ * (n + 1) ^ D₀) := by
          rw [← pow_mul, Nat.mul_comm (A₀ * (n + 1) ^ D₀) k, Nat.mul_assoc]
  have h3 : p.eval (f n) ≤ 2 ^ (k * A₀ * (n + 1) ^ D₀) + k :=
    h1.trans (Nat.add_le_add_right h2 k)
  have hY : 1 ≤ 2 ^ (k * A₀ * (n + 1) ^ D₀) := Nat.one_le_two_pow
  have hk2 : k ≤ 2 ^ (k * A₀ * (n + 1) ^ D₀) * k := by
    calc k = 1 * k := (Nat.one_mul k).symm
      _ ≤ 2 ^ (k * A₀ * (n + 1) ^ D₀) * k := Nat.mul_le_mul hY (le_refl k)
  have hT : k * A₀ * (n + 1) ^ D₀ + (k + 1) ≤ (k * A₀ + k + 1) * (n + 1) ^ D₀ := by
    have hb : 1 ≤ (n + 1) ^ D₀ := Nat.one_le_pow _ _ (Nat.succ_pos n)
    have he : (k * A₀ + k + 1) * (n + 1) ^ D₀
        = k * A₀ * (n + 1) ^ D₀ + (k + 1) * (n + 1) ^ D₀ := by ring
    omega
  have h4 : 2 ^ (k * A₀ * (n + 1) ^ D₀) + k ≤ 2 ^ ((k * A₀ + k + 1) * (n + 1) ^ D₀) := by
    calc 2 ^ (k * A₀ * (n + 1) ^ D₀) + k
        ≤ 2 ^ (k * A₀ * (n + 1) ^ D₀) + 2 ^ (k * A₀ * (n + 1) ^ D₀) * k :=
          Nat.add_le_add (le_refl _) hk2
      _ = 2 ^ (k * A₀ * (n + 1) ^ D₀) * (k + 1) := by ring
      _ ≤ 2 ^ (k * A₀ * (n + 1) ^ D₀) * 2 ^ (k + 1) :=
          Nat.mul_le_mul (le_refl _) (Nat.lt_two_pow_self (k + 1)).le
      _ = 2 ^ (k * A₀ * (n + 1) ^ D₀ + (k + 1)) := by rw [← pow_add]
      _ ≤ 2 ^ ((k * A₀ + k + 1) * (n + 1) ^ D₀) :=
          Nat.pow_le_pow_right (by norm_num) hT
  exact h3.trans h4
